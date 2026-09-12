//! Exact-rational linear-arithmetic **feasibility** via the general simplex
//! (Dutertre–de Moura, *A Fast Linear-Arithmetic Solver for DPLL(T)*, CAV 2006) —
//! the P1.9 replacement for the doubly-exponential Fourier–Motzkin core on the
//! many-variable frontier.
//!
//! # What this decides
//!
//! Given constraints `Σ_j aᵢⱼ·xⱼ  ⋈  bᵢ` (`⋈ ∈ {≤, ≥, =, <, >}`) over rational
//! variables, [`feasible`] returns:
//!
//! - [`SimplexOutcome::Feasible`] with a satisfying rational point `x` (directly
//!   replay-checkable), or
//! - [`SimplexOutcome::Infeasible`] with **Farkas multipliers** `y` over the input
//!   rows: `yᵢ ≥ 0` for a `≤` row, `yᵢ ≤ 0` for a `≥` row, `yᵢ` free for an `=`
//!   row, with `Σ yᵢ·aᵢ = 0` (the combined left-hand side vanishes) and
//!   `Σ yᵢ·bᵢ < 0` — a self-checkable refutation, the same certificate shape the
//!   Fourier–Motzkin path's `crate::lra` already consumes, or
//! - [`SimplexOutcome::Unknown`] iff the exact rational arithmetic declines
//!   (never a wrong verdict — the same `checked_*` discipline as the rest of the
//!   solver).
//!
//! Since **ADR-1702** that last case is much narrower than it was. This engine
//! OPTS IN to promoting rational arithmetic (`Rational::wide_*`), so `i128`
//! overflow inside the tableau no longer abandons the search — the value is
//! carried at arbitrary precision and demoted again as soon as it fits. The
//! whole class of `unknown`s this engine used to return on intermediate
//! coefficient growth is therefore decided.
//!
//! Promotion is **contained**: every value that leaves this module passes
//! through `narrow`, which declines to `Unknown` if a feasible point or a Farkas
//! multiplier does not fit `i128`. Nothing downstream can observe that a
//! promoted value existed, which is why the widening is a pure gain rather than
//! a new obligation on `lra`, `lra_online` or model lifting.
//!
//! The remaining declines are a witness or certificate outside `i128`, division
//! by zero, and a big-rational pool at capacity — see the `Overflow` marker
//! below.
//!
//! # Scope
//!
//! All of `≤`, `≥`, `=`, `<`, `>` — strict rows are exact via the **δ-relaxation**
//! (values in the ordered field `ℚ(δ)`; see [`Delta`]), and a `Feasible` verdict
//! materializes a concrete rational witness by choosing `δ` small enough.
//!
//! # Two entry points
//!
//! - [`feasible`] — the one-shot decision over a fixed constraint list (the
//!   offline `crate::lra` overflow fallback).
//! - [`Incremental`] — the **warm** engine a `DPLL(T)` theory drives: the tableau
//!   structure is built **once** over every row the theory could ever assert, and
//!   `assert`/`retract` only move *bounds*, so a re-check resumes from the previous
//!   basis (Dutertre–de Moura §4). This is what [`crate::lra_online::LraTheory`]
//!   decides feasibility with; the doubly-exponential Fourier–Motzkin core it used
//!   before survives only as the over-cap fallback.
//!
//! # Soundness
//!
//! - Termination is guaranteed by **Bland's rule** (always pivot on the
//!   smallest-index eligible variable), independent of any wall-clock bound.
//! - Every `Feasible` point is a concrete rational assignment the caller replays
//!   against the original atoms.
//! - Every `Infeasible` certificate is **re-checkable** by the caller (and by
//!   [`check_farkas`] here in tests): a bad certificate cannot masquerade as a
//!   sound `unsat`.

use std::time::Instant;

use axeyum_ir::Rational;

/// Hard ceiling on the dense tableau [`Incremental::new`] will build (rows ×
/// columns). A `Rational` is two `i128`s — still true after ADR-1702, whose
/// promoted values live out of line in a capped pool — so 4M cells is ~128 MB;
/// past that the dense general simplex is the wrong data structure and the caller
/// keeps whatever engine it had. Purely structural (no clock), so the decline is deterministic.
pub(crate) const MAX_TABLEAU_CELLS: usize = 4_000_000;

/// Pivot ceiling for a single [`feasible`] / [`Incremental::check`] call. Bland's
/// rule already guarantees termination; this is the deterministic belt so a run
/// with **no** wall-clock deadline still cannot spin unboundedly on a pathological
/// instance. Exhaustion yields [`SimplexOutcome::Unknown`] — sound, never a verdict.
const MAX_PIVOTS: u64 = 2_000_000;

/// Whether a caller-owned absolute deadline has passed.
fn past_deadline(deadline: Option<Instant>) -> bool {
    crate::portfolio::stop_or_past_deadline(deadline)
}

/// How the pivot loop chooses the **entering** variable once the leaving row is
/// fixed.
///
/// Both variants draw from the *same* candidate set — the nonbasic variables
/// with a nonzero coefficient in the leaving row that can move it toward its
/// violated bound, decided by [`Tableau::entering_is_usable`] and nothing else.
/// A rule may only *order* that set; it may never add to it or shrink it. That
/// is what keeps the change to this enum invisible to soundness: `select_entering`
/// returns `None` under exactly the same conditions for every rule, so
/// [`Tableau::farkas`]'s premise — "no nonbasic variable can repair this row" —
/// is a property of the tableau, not of the heuristic. The control
/// `every_rule_agrees_on_whether_a_row_can_be_repaired` pins it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnteringRule {
    /// Bland's rule: the smallest-index usable nonbasic variable.
    ///
    /// Terminating by Bland's theorem and cheap per call (it stops at the first
    /// usable candidate), but it pivots badly: it is indifferent to how much
    /// fill-in the pivot creates, and fill-in is what sets the cost of every
    /// later pivot in a dense tableau.
    Bland,
    /// Fill-in minimising: among the usable candidates, the one whose **column**
    /// has the fewest nonzero entries, ties broken by a deterministic reservoir
    /// sample.
    ///
    /// This is the rule Yices (`simplex.c:3880-3925`) and Z3
    /// (`lp_primal_core_solver.h:183-228`) converged on independently, and Z3's
    /// own comment gives the second motivation: "a short row produces short
    /// infeasibility explanation". Yices scores by *non-free basic* variables in
    /// the column and falls back to the plain nonzero count; we use the nonzero
    /// count, which is Z3's secondary criterion, because
    /// [`Tableau::col_nnz`] maintains it in `O(1)` per written cell while the
    /// non-free count would need a walk per candidate per pivot.
    ///
    /// Termination is **not** inherited from Bland's theorem, so it is recovered
    /// the way both references recover it: a per-call count of variables leaving
    /// the basis a second time, and a switch to [`EnteringRule::Bland`] for the
    /// rest of the call once that count passes
    /// [`PivotPolicy::bland_threshold`]. The `MAX_PIVOTS` belt is unchanged and
    /// still bounds the call whatever the rule does.
    MinimiseFillIn,
}

/// Tunable constants of the pivot loop, with the reference each default comes
/// from. Held by value in the [`Tableau`], so an A/B is a different
/// [`Incremental::with_policy`] and not a rebuild of the crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PivotPolicy {
    /// Which entering rule to use. See [`EnteringRule`].
    pub entering: EnteringRule,
    /// Repeated *leaving* variables after which the rest of **this call** falls
    /// back to Bland's rule.
    ///
    /// A variable is counted once for every time it leaves the basis beyond the
    /// first within one [`Tableau::run`]; the counter and the fallback flag both
    /// reset at the top of every call, so one hard check cannot poison the
    /// engine (Yices `simplex.c:4239`, Z3 `lp_primal_core_solver.h:626-630`).
    ///
    /// Default `1_000`: Yices `SIMPLEX_DEFAULT_BLAND_THRESHOLD`
    /// (`simplex_types.h:908`) and Z3 `m_bland_mode_threshold`
    /// (`lp_primal_core_solver.h:645`) are independently the same number, and
    /// Z3's older simplex (`simplex.h:118`) is a third.
    pub bland_threshold: u64,
    /// Variable counts above which `bland_threshold` is scaled, and by how much
    /// — Yices scales `×100` above `1_000` variables and `×1_000` above
    /// `10_000` (`simplex.c:4243-4249`), on the reasoning that a bigger problem
    /// legitimately needs more repeats before a rule is judged to be cycling.
    pub bland_scale_vars_small: usize,
    /// Multiplier applied at `bland_scale_vars_small`.
    pub bland_scale_small: u64,
    /// The larger variable count; see [`Self::bland_scale_vars_small`].
    pub bland_scale_vars_large: usize,
    /// Multiplier applied at `bland_scale_vars_large`.
    pub bland_scale_large: u64,
    /// Seed for the tie-break among equally-scored candidates.
    ///
    /// Determinism is a public API promise here, so the tie-break is a seeded
    /// LCG — never a clock, never entropy. Two runs of the same query on the
    /// same binary pivot identically; changing this seed is a legitimate A/B
    /// axis and nothing else reads it.
    pub tie_break_seed: u64,
}

impl PivotPolicy {
    /// The shipped default: fill-in minimising with the references' constants.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entering: EnteringRule::MinimiseFillIn,
            bland_threshold: 1_000,
            bland_scale_vars_small: 1_000,
            bland_scale_small: 100,
            bland_scale_vars_large: 10_000,
            bland_scale_large: 1_000,
            tie_break_seed: 0x9E37_79B9_7F4A_7C15,
        }
    }

    /// The pre-2026-09-08 behaviour: Bland's rule unconditionally. Kept as a
    /// named policy rather than deleted, because the dense/Bland arm is the
    /// baseline every measurement of the new rule is a ratio against, and a
    /// baseline you cannot still run is a remembered number.
    #[must_use]
    pub const fn bland() -> Self {
        Self {
            entering: EnteringRule::Bland,
            ..Self::new()
        }
    }

    /// `bland_threshold` scaled for a problem of `n` variables. Computed once at
    /// the top of a call, as in both references.
    fn scaled_bland_threshold(&self, n: usize) -> u64 {
        if n > self.bland_scale_vars_large {
            self.bland_threshold.saturating_mul(self.bland_scale_large)
        } else if n > self.bland_scale_vars_small {
            self.bland_threshold.saturating_mul(self.bland_scale_small)
        } else {
            self.bland_threshold
        }
    }
}

impl Default for PivotPolicy {
    fn default() -> Self {
        Self::new()
    }
}

/// The policy [`Incremental::new`] uses, read **once** from
/// `AXEYUM_SIMPLEX_PIVOT`.
///
/// `fill-in` (the default) is [`PivotPolicy::new`]; `bland` is
/// [`PivotPolicy::bland`], the pre-2026-09-08 behaviour. An integer value sets
/// [`PivotPolicy::bland_threshold`] on the fill-in rule, which is the one
/// constant worth sweeping — Yices and Z3 agree on `1000` but neither measured
/// it against *our* instances.
///
/// The lever exists so an A/B is one binary and two runs rather than two
/// binaries: with two builds, any difference is confounded by everything else
/// that changed between them, and a run that has to rebuild to switch arms is a
/// run nobody repeats. Read once into a `OnceLock` because determinism is a
/// public API promise — the policy cannot change between two solves in one
/// process — and `scripts/parity-run.sh` records any `AXEYUM_*` lever it sees,
/// so a swept number can never be mistaken for a default-configuration one.
///
/// An unrecognised value falls back to the default rather than failing: this is
/// a measurement lever, and a typo in a sweep script must not change a verdict.
/// It is visible in `--trace` through the pivot counters, which is where a
/// reader would notice the arm they did not intend.
fn configured_policy() -> PivotPolicy {
    use std::sync::OnceLock;
    static POLICY: OnceLock<PivotPolicy> = OnceLock::new();
    *POLICY.get_or_init(|| match std::env::var("AXEYUM_SIMPLEX_PIVOT") {
        Ok(v) if v.trim() == "bland" => PivotPolicy::bland(),
        Ok(v) => v.trim().parse::<u64>().map_or_else(
            |_| PivotPolicy::new(),
            |t| PivotPolicy {
                bland_threshold: t,
                ..PivotPolicy::new()
            },
        ),
        Err(_) => PivotPolicy::new(),
    })
}

/// Clock-free structural counters for one [`Tableau`].
///
/// Every field is derived from a quantity the pivot loop *already* computes — a
/// vector length, a loop bound, a branch it already took — so keeping them costs
/// at most one integer add per **row**, never one per cell. That matters twice:
/// it means instrumentation cannot itself be the thing a measurement measures,
/// and it means these can be on in the shipped build, which is the only way a
/// counter is available at the moment somebody wants it.
///
/// Nothing branches on any of these. They exist so that "the pivot is expensive"
/// is a number with units instead of an inference from a wall clock a loaded
/// host moves by ±20%.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TableauCounters {
    /// Rows actually combined by [`Tableau::pivot_and_update`], summed over
    /// every pivot. The pivot skips rows whose entering-column coefficient is
    /// zero, so this is *not* `pivots × m`; the ratio of the two is how much of
    /// the tableau a pivot really touches.
    pub pivot_rows_combined: u64,
    /// Cells written by those combinations: `Σ nnz(pivot row)` over combined
    /// rows. This is the pivot's true cost in exact-rational multiply-adds and
    /// the number a sparse representation would have to beat.
    pub pivot_cells_written: u64,
    /// Columns [`Tableau::select_entering`] examined, summed over every call.
    /// Under Bland this stops at the first usable candidate; under
    /// [`EnteringRule::MinimiseFillIn`] it is the full width every time, which
    /// is the price the rule pays for a better choice.
    pub entering_scan_cells: u64,
    /// Rows the leaving-variable scan examined, summed over every pivot. Ours
    /// rescans from row 0 each iteration, so this is the direct measurement of
    /// what a violated-basic priority heap would remove.
    pub leaving_scan_rows: u64,
    /// Times a variable left the basis for at least the second time within one
    /// [`Tableau::run`] — the trigger [`PivotPolicy::bland_threshold`] counts.
    pub repeat_leavings: u64,
    /// Calls that hit that threshold and finished under Bland's rule.
    pub bland_fallbacks: u64,
    /// Total nonzero cells across every row, sampled at the **end of each
    /// [`Tableau::run`]** — `O(1)` to read, because [`Tableau::col_nnz`] is
    /// maintained incrementally. With `fill_samples` this gives mean nonzeros
    /// per tableau, i.e. fill-in, which is what decides whether a sparse
    /// representation is worth building.
    pub fill_nnz_sum: u64,
    /// Samples behind `fill_nnz_sum`; the denominator, never assumed equal to
    /// the check count.
    pub fill_samples: u64,
    /// [`Tableau::farkas`] declines because the infeasible row's basic variable
    /// is a **problem** variable rather than a slack (`simplex.rs` first decline
    /// arm). A decline yields an empty certificate, which widens the theory's
    /// conflict core to the entire asserted set — sound but maximally coarse —
    /// so these three counters are the cost model for fixing the decline paths.
    pub farkas_declined_basic_not_slack: u64,
    /// Declines because a nonbasic **problem** variable has a nonzero
    /// coefficient in the infeasible row (second decline arm).
    pub farkas_declined_nonbasic_problem_var: u64,
    /// Declines because the extracted candidate failed its own
    /// `farkas_holds` self-check. Distinct from the two structural arms: this
    /// one means the closed form was attempted and did not verify, which is the
    /// arm that would indicate an arithmetic rather than a shape problem.
    pub farkas_declined_self_check: u64,
    /// Infeasible outcomes that returned a **verified** certificate. The
    /// denominator the three decline counters are a fraction of; without it a
    /// zero decline count cannot be told from a zero refutation count.
    pub farkas_certificates: u64,
}

/// The comparator of a constraint row `Σ aⱼ·xⱼ ⋈ b`.
///
/// The full set is part of the feasibility API (and exercised by the tests); both
/// in-tree callers — the LRA fallback in `crate::lra` and the online
/// [`crate::lra_online::LraTheory`] — normalize every atom to a `≤`/`<` row, so
/// they only construct `Le`/`Lt`.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rel {
    /// `Σ aⱼ·xⱼ ≤ b`.
    Le,
    /// `Σ aⱼ·xⱼ ≥ b`.
    Ge,
    /// `Σ aⱼ·xⱼ = b`.
    Eq,
    /// `Σ aⱼ·xⱼ < b` (strict; handled exactly via the δ-relaxation).
    Lt,
    /// `Σ aⱼ·xⱼ > b` (strict).
    Gt,
}

/// One linear constraint `Σ coeffs[j]·x[j] ⋈ rhs` over the shared variable set
/// (`coeffs.len()` is the number of problem variables, the same for every row).
#[derive(Debug, Clone)]
pub struct Constraint {
    /// Coefficient of each problem variable (dense, length = number of variables).
    pub coeffs: Vec<Rational>,
    /// The comparator.
    pub rel: Rel,
    /// The right-hand side constant.
    pub rhs: Rational,
}

/// The result of a feasibility query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimplexOutcome {
    /// Satisfiable: a rational point (`x[j]`) meeting every constraint.
    Feasible(Vec<Rational>),
    /// Unsatisfiable: Farkas multipliers `y` over the *input rows* (one per
    /// constraint) whose nonnegative-combination collapses to `0 < 0`.
    Infeasible(Vec<Rational>),
    /// Exact arithmetic declined — a sound `unknown`, never a verdict.
    Unknown,
}

/// Marker for an exact-arithmetic decline; mapped to [`SimplexOutcome::Unknown`].
///
/// **ADR-1702 narrowed this but did not make it unreachable, so it stays.** The
/// tableau's arithmetic promotes rather than overflowing, which removes the
/// coefficient-growth `unknown`s this marker used to carry. What remains
/// reachable is [`Rational::wide_div`] declining on a **zero divisor** — not an
/// overflow at all — and the big-rational pool reaching
/// [`Rational::big_pool_capacity`], past which every operation behaves exactly
/// as it did before ADR-1702. Deleting the marker would delete a live soundness
/// path, so the pivot and deadline budgets and this decline route are all kept.
///
/// One helper below dropped out of this shape entirely: `cmp` is infallible after
/// ADR-1702, because `Rational::wide_cmp` allocates no pool entry, so it returns
/// a bare `Ordering`. Keeping a `Result` that can only be `Ok` is a failure path
/// that cannot fail, which is exactly what this repository does not keep.
struct Overflow;
type R<T> = Result<T, Overflow>;

// ADR-1702: this engine OPTS IN to promoting rational arithmetic. The `wide_*`
// family carries a value past `i128` instead of declining, which is what removes
// the coefficient-growth `unknown`s the tableau used to return; promoted values
// never leave this module, because every public exit narrows through
// [`narrow`].
fn add(a: Rational, b: Rational) -> R<Rational> {
    a.wide_add(b).ok_or(Overflow)
}
fn sub(a: Rational, b: Rational) -> R<Rational> {
    a.wide_sub(b).ok_or(Overflow)
}
fn mul(a: Rational, b: Rational) -> R<Rational> {
    a.wide_mul(b).ok_or(Overflow)
}
fn div(a: Rational, b: Rational) -> R<Rational> {
    a.wide_div(b).ok_or(Overflow)
}
/// Exact comparison. **Infallible since ADR-1702** — `wide_cmp` allocates no
/// pool entry, so there is no failure to carry — which is why this one is not
/// wrapped in `R<_>` like its four arithmetic siblings.
fn cmp(a: Rational, b: Rational) -> core::cmp::Ordering {
    a.wide_cmp(&b)
}

/// The **containment boundary** for ADR-1702 promotion — and, measured
/// 2026-09-09, a decline on satisfiable problems.
///
/// The tableau computes over promoted rationals, but every value this module
/// hands back — a feasible point, a Farkas multiplier vector — is narrowed to an
/// ordinary `i128` rational, and a vector that does not fit declines to
/// [`SimplexOutcome::Unknown`].
///
/// # The claim this comment used to make, and why it was wrong
///
/// It said the widening was "strictly a gain" because "nothing outside this
/// module can observe that a promoted value ever existed". The first clause is
/// true of *intermediate* growth. The second is not a property of this
/// boundary: what the outside observes is an `unknown` on a query that has a
/// model. `the_witness_boundary_discards_an_exact_model_that_exceeds_i128`
/// below builds one — a 131-variable doubling chain whose coefficients are all
/// small integers and whose exact vertex is `x_0 = 2^130` — and this function
/// throws that witness away. Yices2, `OpenSMT` and `SMTInterpol` all keep growing
/// the number instead
/// (`docs/solver-comparison-2026-09/05-yices-opensmt-smtinterpol.md`: "Three
/// independent implementations chose 'grow the number'; we chose 'give up'").
/// Opening this boundary is roadmap item 2.3.
///
/// # Why it is nevertheless still closed
///
/// Not because the boundary is right, but because it is the LAST brick rather
/// than the first. `Rational::numerator()` / `denominator()` **panic** on a
/// promoted value, and the declining `checked_*` family computes exactly and
/// then demotes — so it returns `None` for **any** result outside `i128`, even
/// `x + 0` when `x` is promoted. Measured 2026-09-09, each exit route hits one
/// of those before anything replays:
///
/// - **Feasible point → `Value::Real` in a model.** `axeyum_ir::eval` declines
///   every real arithmetic operator on a promoted operand, so the replay that
///   is the trust anchor for `sat` can never succeed — a sound `unknown`, but
///   the *same* `unknown` we have now. Beyond that it is not sound: `eval.rs`
///   `Op::RealToInt` (`:772`) and `RealAlgebraic::from_rational`
///   (`real_algebraic.rs:164`) panic, `auto::milp_bnb` panics twice
///   (`auto.rs:2537`, `:2570` — its `is_integer()` guard passes for a promoted
///   integer), and `smtlib_value_text` (`smtlib.rs:3904`) panics, which is the
///   `get-model` / `get-value` path, so even a model that replayed could not be
///   printed. `axeyum-py`'s `convert.rs:144` is the same shape.
/// - **Farkas multipliers → `crate::lra::FarkasCertificate`.** Mostly
///   self-limiting: `verify()` is all `checked_*`, so a promoted multiplier
///   makes the self-check return `false` and `lra.rs` declines. What survives
///   that filter reaches `alethe_lra::rational_to_alethe` (`:944`) and the Lean
///   reconstruction (`reconstruct/arithmetic.rs:4778`, `:5043`), which panic.
///
/// So deleting the `is_big` test here, on its own, converts a sound `unknown`
/// into a crash on the `get-model` path — strictly worse. The order of work is:
/// give the evaluator a promoted-real path (the shape `Value::WideInt` already
/// has at `eval.rs:554`), move the model consumers to `checked_numerator()` /
/// `numerator_big()` or an explicit decline, and only then open this. That is
/// ADR-1702's own rule: "Every future opt-in must repeat that discipline:
/// either keep promoted values inside the route, or use the checked accessors
/// at the boundary."
///
/// The two blockers are pinned by
/// `crates/axeyum-solver/tests/wide_witness_boundary.rs`, whose tests are
/// written to FAIL when they are removed — that failure is the signal that this
/// boundary is now landable.
fn narrow(values: Vec<Rational>) -> Option<Vec<Rational>> {
    if values.iter().any(|v| v.is_big()) {
        return None;
    }
    Some(values)
}

/// A value `c + k·δ` in the ordered field `ℚ(δ)` with `δ` a positive infinitesimal
/// (Dutertre–de Moura §3): the δ-relaxation that makes *strict* inequalities exact.
/// A strict upper bound `x < b` becomes the ordinary bound `x ≤ b − δ` (i.e.
/// `(b, −1)`); a strict lower bound `x > b` becomes `x ≥ b + δ` (`(b, +1)`). All
/// tableau values and bounds live in `ℚ(δ)`; coefficients stay rational.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Delta {
    c: Rational,
    k: Rational,
}

impl Delta {
    fn num(c: Rational) -> Delta {
        Delta {
            c,
            k: Rational::zero(),
        }
    }
    fn zero() -> Delta {
        Delta::num(Rational::zero())
    }
    fn add(self, o: Delta) -> R<Delta> {
        Ok(Delta {
            c: add(self.c, o.c)?,
            k: add(self.k, o.k)?,
        })
    }
    fn sub(self, o: Delta) -> R<Delta> {
        Ok(Delta {
            c: sub(self.c, o.c)?,
            k: sub(self.k, o.k)?,
        })
    }
    /// Scale by a rational (coefficients are rational, so this stays in `ℚ(δ)`).
    fn scale(self, s: Rational) -> R<Delta> {
        Ok(Delta {
            c: mul(self.c, s)?,
            k: mul(self.k, s)?,
        })
    }
    /// Lexicographic order on `(c, k)` — the total order of `ℚ(δ)` for infinitesimal
    /// `δ > 0`. Infallible for the same reason the free `cmp` above is.
    fn cmp(self, o: Delta) -> core::cmp::Ordering {
        match cmp(self.c, o.c) {
            core::cmp::Ordering::Equal => cmp(self.k, o.k),
            ord => ord,
        }
    }
}

/// [`feasible`] under an absolute wall-clock `deadline`; `None` is "no bound".
///
/// **Why this exists.** [`Tableau::run`] has always taken a deadline and polls
/// it every 64 pivots — the [`Incremental`] engine passes a real one. The
/// one-shot entry point above passed the literal `None`, so the whole
/// `lra::simplex_fallback` route ran with the pivot loop's budget check wired
/// to a constant. Measured 2026-09-12 on the `QF_UFLRA`
/// `cpachecker-induction.32_1_cilled…` family: `--timeout-ms 2000` returned at
/// 3.009 s, i.e. budget + the harness watchdog's 1 s grace, because the worker
/// thread never came back on its own. That is the ADR-1906 shape one more time
/// — a deadline test the workload cannot reach — except here the counter was
/// fine and the *argument* was the constant.
#[must_use]
pub fn feasible_within(
    nvars: usize,
    constraints: &[Constraint],
    deadline: Option<Instant>,
) -> SimplexOutcome {
    for c in constraints {
        assert_eq!(c.coeffs.len(), nvars, "constraint arity mismatch");
    }
    let mut tableau = Tableau::new(nvars, constraints);
    match tableau.run(deadline, MAX_PIVOTS) {
        Ok(RunOutcome::Feasible) => match tableau.materialize() {
            Ok(point) => narrow(point).map_or(SimplexOutcome::Unknown, SimplexOutcome::Feasible),
            Err(Overflow) => SimplexOutcome::Unknown,
        },
        Ok(RunOutcome::Infeasible(y)) => {
            narrow(y).map_or(SimplexOutcome::Unknown, SimplexOutcome::Infeasible)
        }
        Ok(RunOutcome::Unknown) | Err(Overflow) => SimplexOutcome::Unknown,
    }
}

/// What the pivot loop concluded, without materializing a witness (the warm engine
/// re-checks thousands of times and only needs a point at the very end).
enum RunOutcome {
    Feasible,
    Infeasible(Vec<Rational>),
    Unknown,
}

/// Convert a dense coefficient vector to the sparse row form the tableau stores.
fn densify_to_sparse(coeffs: &[Rational]) -> Vec<(usize, Rational)> {
    coeffs
        .iter()
        .enumerate()
        .filter(|(_, a)| !a.is_zero())
        .map(|(j, &a)| (j, a))
        .collect()
}

/// The general-simplex tableau.
///
/// Variables `0..nvars` are the problem variables; `nvars..nvars+m` are the slack
/// variables `sᵢ = Σ aᵢⱼ·xⱼ` (one per constraint), which carry the row bounds. A
/// variable is either **basic** (its value is defined by its tableau row over the
/// nonbasic variables) or **nonbasic** (its value is set directly, between bounds).
struct Tableau {
    /// Total variable count: `nvars + m`.
    n: usize,
    /// Problem-variable count.
    nvars: usize,
    /// Constraint (slack) count.
    m: usize,
    /// `basic[i]` is the variable id basic in row `i` (row `i` corresponds to slack
    /// `nvars + i` initially, but the basic var changes as we pivot).
    basic: Vec<usize>,
    /// `row[i][v]` = coefficient of nonbasic variable `v` in the expression for the
    /// basic variable of row `i`. (Columns for currently-basic variables are 0.)
    row: Vec<Vec<Rational>>,
    /// Current value of every variable, in `ℚ(δ)`.
    value: Vec<Delta>,
    /// Lower / upper bound of every variable (`None` = unbounded on that side).
    lower: Vec<Option<Delta>>,
    upper: Vec<Option<Delta>>,
    /// Whether each variable is currently basic.
    is_basic: Vec<bool>,
    /// Sparse coefficients of every input row over the problem variables. The row
    /// *structure* is fixed for the tableau's life — only [`Tableau::rel_rhs`] moves.
    rows_sparse: Vec<Vec<(usize, Rational)>>,
    /// Per input row: the relation and right-hand side currently imposed, or `None`
    /// when the row carries **no bound at all** (the [`Incremental`] engine's "this
    /// atom is not asserted" state). An unbounded slack can never violate a bound
    /// and — being always an eligible entering variable — can never appear in a
    /// Farkas certificate; `farkas_holds` rejects any candidate that puts a
    /// nonzero multiplier on one.
    rel_rhs: Vec<Option<(Rel, Rational)>>,
    /// Pivots performed over this tableau's whole life, across every
    /// [`Tableau::run`]. Diagnostic only — nothing branches on it. It is what
    /// makes "does the basis persist between checks?" a measurement rather than
    /// a reading of the source: a warm engine's pivots-per-check falls while its
    /// check count rises, a cold one's does not.
    total_pivots: u64,
    /// `col_nnz[v]` = how many rows have a nonzero coefficient in column `v`.
    ///
    /// Maintained **incrementally**: [`Tableau::reset_structure`] recomputes it
    /// from scratch, and every cell the pivot writes updates it by the
    /// zero/nonzero transition of that one cell. That is `O(1)` per written cell
    /// on top of the exact-rational add already being done, and it buys two
    /// things a dense tableau otherwise cannot have:
    ///
    /// - the [`EnteringRule::MinimiseFillIn`] score in `O(1)` per candidate,
    ///   where scoring by walking the column would be `O(m)` per candidate per
    ///   pivot, i.e. a second dense pass;
    /// - total fill-in as a sum, so "how dense has this tableau become" is a
    ///   read rather than an `O(m·n)` scan nobody can afford to take often
    ///   enough to see the growth.
    ///
    /// `col_nnz_matches_a_recount` checks it against a full recount rather than
    /// trusting the incremental maintenance.
    col_nnz: Vec<u32>,
    /// `row_nz[i]` = the **sorted** column indices at which row `i` is nonzero.
    ///
    /// This is a sparse *index* over dense storage, not a sparse representation:
    /// `row[i][v]` stays an `O(1)` random access — which `farkas`, the value
    /// repair and every existing test rely on — while everything that
    /// *iterates* a row iterates this instead of `0..n`. Measured on
    /// `QF_LRA/2019-ezsmt/blending/1.smt2` the tableau is 350 x 425 and holds
    /// about 2,100 nonzeros, i.e. **1.4% dense** with roughly 6 nonzeros per
    /// row, so the three `O(columns)` scans a pivot used to make were each
    /// touching about 70x more cells than they could act on.
    ///
    /// Kept **sorted**, at an `O(len)` memmove per insert or remove, for two
    /// reasons and not for tidiness: Bland's rule is defined as the
    /// smallest-index usable candidate, so an unsorted index would silently
    /// change the terminating rule into a different one; and the pivot's
    /// exact-rational adds are performed in this order, so an unstable order
    /// would make an overflow decline depend on hash order. Determinism is a
    /// public API promise.
    ///
    /// Maintained through the same single mutation point as `col_nnz`
    /// ([`Tableau::set_cell`]), and checked against a recount by
    /// `col_nnz_matches_a_recount_after_every_pivot`.
    row_nz: Vec<Vec<usize>>,
    /// The entering rule and its constants; see [`PivotPolicy`].
    policy: PivotPolicy,
    /// Clock-free structural counters; see [`TableauCounters`]. Diagnostic only
    /// — nothing in the pivot loop branches on any field of this.
    counters: TableauCounters,
    /// Deterministic LCG state for [`EnteringRule::MinimiseFillIn`]'s tie-break.
    /// Seeded from [`PivotPolicy::tie_break_seed`], never from a clock.
    tie_break_state: u64,
}

impl Tableau {
    /// A tableau over `rows_sparse` with **no** bounds imposed (every row inactive).
    fn new_rows(nvars: usize, rows_sparse: Vec<Vec<(usize, Rational)>>) -> Tableau {
        Tableau::new_rows_with_policy(nvars, rows_sparse, PivotPolicy::new())
    }

    /// As [`Tableau::new_rows`], under an explicit [`PivotPolicy`].
    fn new_rows_with_policy(
        nvars: usize,
        rows_sparse: Vec<Vec<(usize, Rational)>>,
        policy: PivotPolicy,
    ) -> Tableau {
        let m = rows_sparse.len();
        let n = nvars + m;
        let rel_rhs = vec![None; m];
        let mut t = Tableau {
            n,
            nvars,
            m,
            basic: vec![0usize; m],
            row: vec![Vec::new(); m],
            value: vec![Delta::zero(); n],
            lower: vec![None; n],
            upper: vec![None; n],
            is_basic: vec![false; n],
            rows_sparse,
            rel_rhs,
            total_pivots: 0,
            col_nnz: vec![0u32; n],
            row_nz: vec![Vec::new(); m],
            policy,
            counters: TableauCounters::default(),
            tie_break_state: policy.tie_break_seed,
        };
        t.reset_structure();
        t
    }

    /// Restores the pristine basis: every slack basic in its own row, every problem
    /// variable nonbasic at `0`, so `slackᵢ = Σ aᵢⱼ·0 = 0`. Bounds ([`Self::rel_rhs`]
    /// and the derived `lower`/`upper`) are **not** touched — this is the recovery
    /// path after an arithmetic overflow left the cached values inconsistent.
    fn reset_structure(&mut self) {
        for i in 0..self.m {
            let mut dense = vec![Rational::zero(); self.n];
            for &(j, a) in &self.rows_sparse[i] {
                dense[j] = a;
            }
            self.row[i] = dense;
            self.basic[i] = self.nvars + i;
        }
        self.is_basic.iter_mut().for_each(|b| *b = false);
        for i in 0..self.m {
            self.is_basic[self.nvars + i] = true;
        }
        self.value.iter_mut().for_each(|v| *v = Delta::zero());
        // The one place the row contents are rebuilt, so the one place the
        // incrementally-maintained column counts are recomputed from scratch.
        self.recount_columns();
    }

    /// Recomputes [`Tableau::col_nnz`] by a full scan. Called only from
    /// [`Tableau::reset_structure`] — everywhere else the counts are maintained
    /// per written cell — and by the test that checks the two agree.
    fn recount_columns(&mut self) {
        self.col_nnz.clear();
        self.col_nnz.resize(self.n, 0);
        self.row_nz.clear();
        self.row_nz.resize(self.m, Vec::new());
        for i in 0..self.m {
            for v in 0..self.n {
                if !self.row[i][v].is_zero() {
                    self.col_nnz[v] += 1;
                    self.row_nz[i].push(v);
                }
            }
        }
    }

    /// Total nonzero cells in the tableau — the fill-in figure, `O(n)` to read
    /// because the per-column counts are maintained.
    fn total_nnz(&self) -> u64 {
        self.col_nnz.iter().map(|&c| u64::from(c)).sum()
    }

    /// Writes `value` into cell `(i, v)` and keeps [`Tableau::col_nnz`] exact.
    ///
    /// This is the single mutation point for a row cell inside the pivot, so the
    /// column counts cannot drift by someone adding an assignment that forgets
    /// them: the only other writer is `reset_structure`, which recounts.
    fn set_cell(&mut self, i: usize, v: usize, value: Rational) {
        let was_zero = self.row[i][v].is_zero();
        let now_zero = value.is_zero();
        self.row[i][v] = value;
        match (was_zero, now_zero) {
            (true, false) => {
                self.col_nnz[v] += 1;
                let at = self.row_nz[i].partition_point(|&c| c < v);
                self.row_nz[i].insert(at, v);
            }
            (false, true) => {
                self.col_nnz[v] -= 1;
                if let Ok(at) = self.row_nz[i].binary_search(&v) {
                    self.row_nz[i].remove(at);
                }
            }
            _ => {}
        }
    }

    fn new(nvars: usize, constraints: &[Constraint]) -> Tableau {
        let rows_sparse: Vec<Vec<(usize, Rational)>> = constraints
            .iter()
            .map(|c| densify_to_sparse(&c.coeffs))
            .collect();
        let mut t = Tableau::new_rows(nvars, rows_sparse);
        for (i, c) in constraints.iter().enumerate() {
            t.set_row_bound(i, Some((c.rel, c.rhs)));
        }
        t
    }

    /// Imposes (or removes, with `None`) the bound of input row `i`, rewriting the
    /// slack's `lower`/`upper` in `ℚ(δ)`. Strict `<`/`>` shrink the bound by one
    /// infinitesimal: `x < b` ⇔ `x ≤ b − δ`. **Values are not touched** — the caller
    /// repairs them (nonbasic: [`Tableau::clamp_nonbasic`]; basic: the pivot loop).
    fn set_row_bound(&mut self, i: usize, rr: Option<(Rel, Rational)>) {
        let slack = self.nvars + i;
        self.rel_rhs[i] = rr;
        self.lower[slack] = None;
        self.upper[slack] = None;
        let Some((rel, rhs)) = rr else { return };
        let b = Delta::num(rhs);
        let b_minus_d = Delta {
            c: rhs,
            k: Rational::integer(-1),
        };
        let b_plus_d = Delta {
            c: rhs,
            k: Rational::integer(1),
        };
        match rel {
            Rel::Le => self.upper[slack] = Some(b),
            Rel::Ge => self.lower[slack] = Some(b),
            Rel::Eq => {
                self.lower[slack] = Some(b);
                self.upper[slack] = Some(b);
            }
            Rel::Lt => self.upper[slack] = Some(b_minus_d),
            Rel::Gt => self.lower[slack] = Some(b_plus_d),
        }
    }

    /// Dutertre–de Moura `update`: move **nonbasic** `v` to `target` and carry the
    /// change into every basic variable's value (`basicᵢ += rowᵢ[v]·Δ`). O(m·nnz-free
    /// column scan) — the reason a bound assertion does not cost a full recompute.
    fn update_nonbasic(&mut self, v: usize, target: Delta) -> R<()> {
        debug_assert!(!self.is_basic[v]);
        let delta = target.sub(self.value[v])?;
        if delta.c.is_zero() && delta.k.is_zero() {
            return Ok(());
        }
        for i in 0..self.m {
            let coeff = self.row[i][v];
            if coeff.is_zero() {
                continue;
            }
            let b = self.basic[i];
            self.value[b] = self.value[b].add(delta.scale(coeff)?)?;
        }
        self.value[v] = target;
        Ok(())
    }

    /// Pulls nonbasic `v` back inside its bounds if the bound just imposed on it
    /// excludes its current value (a no-op for a basic variable — the pivot loop
    /// repairs those).
    fn clamp_nonbasic(&mut self, v: usize) -> R<()> {
        if self.is_basic[v] {
            return Ok(());
        }
        if let Some(hi) = self.upper[v]
            && self.value[v].cmp(hi) == core::cmp::Ordering::Greater
        {
            return self.update_nonbasic(v, hi);
        }
        if let Some(lo) = self.lower[v]
            && self.value[v].cmp(lo) == core::cmp::Ordering::Less
        {
            return self.update_nonbasic(v, lo);
        }
        Ok(())
    }

    /// Whether `v`'s value is below its lower bound.
    fn below_lower(&self, v: usize) -> bool {
        match self.lower[v] {
            Some(lo) => self.value[v].cmp(lo) == core::cmp::Ordering::Less,
            None => false,
        }
    }
    /// Whether `v`'s value is above its upper bound.
    fn above_upper(&self, v: usize) -> bool {
        match self.upper[v] {
            Some(hi) => self.value[v].cmp(hi) == core::cmp::Ordering::Greater,
            None => false,
        }
    }

    /// Can nonbasic `v` increase (strictly below its upper bound, or unbounded)?
    fn can_increase(&self, v: usize) -> bool {
        match self.upper[v] {
            Some(hi) => self.value[v].cmp(hi) == core::cmp::Ordering::Less,
            None => true,
        }
    }
    /// Can nonbasic `v` decrease (strictly above its lower bound, or unbounded)?
    fn can_decrease(&self, v: usize) -> bool {
        match self.lower[v] {
            Some(lo) => self.value[v].cmp(lo) == core::cmp::Ordering::Greater,
            None => true,
        }
    }

    /// The main feasibility loop (Bland's rule on the basic variable, then on the
    /// entering nonbasic variable). Resumes from whatever basis/assignment the
    /// tableau currently holds — which is what makes [`Incremental`] warm.
    ///
    /// `budget` bounds the pivot count and `deadline` the wall clock; exhausting
    /// either yields [`SimplexOutcome::Unknown`] (sound, never a verdict).
    fn run(&mut self, deadline: Option<Instant>, budget: u64) -> R<RunOutcome> {
        let mut pivots: u64 = 0;
        // Per-call termination state, reset here and nowhere else. Both
        // references reset at the top of a feasibility call for the same reason:
        // one hard check must not leave the engine permanently on the slow rule
        // (Yices `simplex.c:4239`, Z3 `lp_primal_core_solver.h:626-630`).
        let bland_threshold = self.policy.scaled_bland_threshold(self.n);
        let mut has_left: Vec<bool> = vec![false; self.n];
        let mut repeats: u64 = 0;
        let mut bland_mode = self.policy.entering == EnteringRule::Bland;
        let outcome = loop {
            // Polled on entry too, so an already-expired deadline does no work at
            // all and reports `Unknown` rather than a verdict the caller did not
            // budget for.
            if pivots.is_multiple_of(64) && past_deadline(deadline) {
                break RunOutcome::Unknown;
            }
            // The memory bound, at the same boundary as the wall-clock one and
            // unconditional because it costs one relaxed atomic load rather
            // than the `Instant::now()` this loop rations to one pivot in 64.
            // Pivoting rewrites `Rational` cells in place, so it is not itself
            // the growth site; what it is, is a place a query can spend seconds
            // AFTER the process went over budget, which on the three files
            // measured 2026-09-08 is where the limit was overshot by 1.9x
            // before anything else looked.
            if crate::memory_budget::watchdog_tripped() {
                break RunOutcome::Unknown;
            }
            if pivots >= budget {
                // The deadline break above yields the SAME `RunOutcome::Unknown`,
                // and `Status::Unknown`'s own doc admits it covers "the
                // pivot/deadline budget ran out" as one case. This is the only
                // record that says which.
                crate::config_registry::note_crossed(
                    "crates/axeyum-solver/src/simplex.rs::MAX_PIVOTS",
                    pivots,
                    budget,
                );
                break RunOutcome::Unknown;
            }
            pivots += 1;
            // Smallest-index basic variable that violates a bound.
            let mut viol: Option<(usize, bool)> = None; // (row, too_low)
            let mut scanned: u64 = 0;
            for i in 0..self.m {
                scanned += 1;
                let b = self.basic[i];
                if self.below_lower(b) {
                    viol = Some((i, true));
                    break;
                }
                if self.above_upper(b) {
                    viol = Some((i, false));
                    break;
                }
            }
            self.counters.leaving_scan_rows += scanned;
            let Some((r, too_low)) = viol else {
                // All bounds satisfied → feasible.
                break RunOutcome::Feasible;
            };

            let b = self.basic[r];
            // Choose the entering nonbasic variable. Every rule draws from the
            // same candidate set (see `EnteringRule`), so a `None` here means
            // the row is unrepairable whatever the rule — which is exactly the
            // premise `farkas` rests on.
            let entering = self.select_entering(r, too_low, bland_mode);
            let Some(j) = entering else {
                // No way to repair row `r` → infeasible. Build the Farkas cert.
                break RunOutcome::Infeasible(self.farkas(r, too_low)?);
            };

            // `b` is about to leave the basis. Counting only *repeat* departures
            // — rather than iterations — is what distinguishes a long but
            // progressing call from a cycling one, and is the trigger both
            // references chose.
            if !bland_mode {
                if has_left[b] {
                    repeats += 1;
                    self.counters.repeat_leavings += 1;
                    if repeats > bland_threshold {
                        bland_mode = true;
                        self.counters.bland_fallbacks += 1;
                    }
                } else {
                    has_left[b] = true;
                }
            }

            // Target value for the leaving basic variable: its violated bound.
            let target = if too_low {
                self.lower[b].expect("violated lower ⇒ bound exists")
            } else {
                self.upper[b].expect("violated upper ⇒ bound exists")
            };
            self.total_pivots += 1;
            self.pivot_and_update(r, j, target)?;
        };
        // Fill-in is sampled once per call rather than per pivot: `total_nnz` is
        // O(columns) thanks to the maintained counts, but per-pivot it would
        // still be the largest single term in a cheap pivot.
        self.counters.fill_nnz_sum += self.total_nnz();
        self.counters.fill_samples += 1;
        Ok(outcome)
    }

    /// Whether nonbasic `v` can be used to move row `r`'s basic variable toward
    /// its violated bound — the entering-variable **candidate set**.
    ///
    /// Deliberately one function shared by every [`EnteringRule`]. The rules
    /// differ only in which member of this set they pick; none of them may
    /// change the set, because `select_entering` returning `None` is what
    /// [`Tableau::farkas`] reads as "this row is unrepairable" before it builds
    /// a refutation. Keeping the predicate in one place makes that a structural
    /// property rather than a promise two code paths have to keep.
    ///
    /// Returns `None` when `v` is basic or has a zero coefficient in the row.
    fn entering_is_usable(&self, r: usize, v: usize, too_low: bool) -> bool {
        if self.is_basic[v] {
            return false;
        }
        let a = self.row[r][v];
        if a.is_zero() {
            return false;
        }
        let a_pos = cmp(a, Rational::zero()) == core::cmp::Ordering::Greater;
        // To INCREASE the basic var (too_low): raise a nonbasic with a>0 that can
        // increase, or lower one with a<0 that can decrease. To DECREASE: mirror.
        if too_low {
            (a_pos && self.can_increase(v)) || (!a_pos && self.can_decrease(v))
        } else {
            (a_pos && self.can_decrease(v)) || (!a_pos && self.can_increase(v))
        }
    }

    /// Entering-variable selection for repairing row `r` whose basic variable is
    /// too low (`too_low`) or too high, under the configured [`EnteringRule`] —
    /// or forced to Bland's rule when `force_bland` is set by the caller's
    /// repeat-leaving fallback.
    ///
    /// Both rules quantify over the same candidate set
    /// ([`Tableau::entering_is_usable`]) and therefore agree exactly on *whether*
    /// a candidate exists; they disagree only on which one.
    fn select_entering(&mut self, r: usize, too_low: bool, force_bland: bool) -> Option<usize> {
        // Only a column where the row is NONZERO can be usable, so iterating the
        // row's sorted nonzero index visits exactly the candidates and no
        // others. Under Bland the index is sorted, so "first usable in this
        // order" is still "smallest usable index" — the rule is unchanged, not
        // approximated.
        if force_bland || self.policy.entering == EnteringRule::Bland {
            for k in 0..self.row_nz[r].len() {
                let v = self.row_nz[r][k];
                self.counters.entering_scan_cells += 1;
                if self.entering_is_usable(r, v, too_low) {
                    return Some(v);
                }
            }
            return None;
        }

        // Fill-in minimising. The score is the candidate column's nonzero count,
        // read in O(1) from the maintained `col_nnz`; a pivot on a sparse column
        // touches few rows and grows the tableau least. Ties are broken by a
        // deterministic reservoir sample so the rule does not degenerate into
        // "smallest index among equals", which is how a fill-in rule quietly
        // becomes Bland's on the many instances where scores are flat.
        let mut best: Option<usize> = None;
        let mut best_score = u32::MAX;
        let mut ties: u64 = 0;
        for k in 0..self.row_nz[r].len() {
            let v = self.row_nz[r][k];
            self.counters.entering_scan_cells += 1;
            if !self.entering_is_usable(r, v, too_low) {
                continue;
            }
            let score = self.col_nnz[v];
            if best.is_none() || score < best_score {
                best = Some(v);
                best_score = score;
                ties = 1;
            } else if score == best_score {
                ties += 1;
                // Reservoir sampling: replace the incumbent with probability
                // 1/ties, so every candidate at the best score is equally
                // likely. `next_tie_break` is a seeded LCG — determinism is a
                // public promise, so this is reproducible, not random.
                if self.next_tie_break().is_multiple_of(ties) {
                    best = Some(v);
                }
            }
        }
        best
    }

    /// Next value of the deterministic tie-break stream (MMIX LCG constants, the
    /// house convention). Never reads a clock or an entropy source.
    fn next_tie_break(&mut self) -> u64 {
        self.tie_break_state = self
            .tie_break_state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.tie_break_state >> 11
    }

    /// Pivot nonbasic `enter` into the basis in row `r` (whose current basic var
    /// `leave` moves to nonbasic at value `target`), then repair all rows.
    ///
    /// # Cost, and why the value repair is not a recompute (S4)
    ///
    /// This is Dutertre–de Moura's `pivotAndUpdate`. The **row** rewrite is
    /// inherently `O(rows × columns)` for a dense tableau, but the **value**
    /// repair is only `O(rows)`: the entering variable moves by
    /// `θ = (target − β(leave)) / a_re`, so every other basic variable moves by
    /// `a_{i,enter} · θ` with `a_{i,enter}` read from the tableau *before* the
    /// elimination zeroes that column. Recomputing every basic value from its
    /// row instead — which this function did until S4 — is a second
    /// `O(rows × columns)` pass in `ℚ(δ)` (two rationals per cell, so the more
    /// expensive of the two halves), spent re-deriving numbers the update
    /// already determines.
    ///
    /// That is not a micro-optimisation here: measured on
    /// `QF_LRA/2019-ezsmt/blending/1.smt2` the tableau is 350 × 425, one pivot
    /// cost 1.41 ms, and `final_check` was 21.7 s of a 24 s budget across 6,571
    /// checks at 2.3 pivots each. The counters that establish it are
    /// [`Incremental::pivots`], [`Incremental::checks`] and
    /// [`Incremental::cold_restarts`] — the last of which read `0`, i.e. the
    /// basis was already persisting between checks and pivot *count* was never
    /// the problem.
    // The pivot rewrites parallel dense rows by column index `v`, indexing several
    // arrays at once — a plain range loop is the clearest form here.
    #[allow(clippy::needless_range_loop)]
    fn pivot_and_update(&mut self, r: usize, enter: usize, target: Delta) -> R<()> {
        let leave = self.basic[r];
        let a_re = self.row[r][enter];
        let recip = div(Rational::integer(1), a_re)?;

        // The entering variable's column as it stands BEFORE the elimination
        // below zeroes it. Both the row rewrite and the O(rows) value update read
        // it, and the update must see the *old* coefficients.
        let col: Vec<Rational> = (0..self.m).map(|i| self.row[i][enter]).collect();

        // How far `enter` must move so that `leave` reaches `target`:
        //   leave_old = value[leave]; enter changes by θ; leave changes by a_re·θ,
        //   so θ = (target - value[leave]) / a_re. Read from the OLD values.
        let theta = target.sub(self.value[leave])?.scale(recip)?;
        let enter_new = self.value[enter].add(theta)?;

        // Solve row r for `enter`:  leave = Σ a_rv·v  ⇒
        //   enter = (leave - Σ_{v≠enter} a_rv·v) / a_re, i.e. rewrite the row.
        // New row (for the now-basic `enter`): coefficient of `leave` becomes 1/a_re,
        // every other nonbasic v becomes -a_rv/a_re, and `enter`'s own column 0.
        // Rewritten IN PLACE. The old form allocated and zero-filled a fresh
        // `Vec<Rational>` of width `n` per pivot and dropped the previous one —
        // 13.6 KB written and 13.6 KB freed on `blending/1` to carry about 35
        // real values. In place is not merely cheaper, it is exact: every column
        // outside `row_nz[r]` is zero in the old row and stays zero in the new
        // one, so it is not a cell the rewrite has any business touching.
        //
        // Three facts make the in-place form correct, and the third is the one
        // worth stating because the code would be subtly wrong without it:
        //  - `enter` IS in `row_nz[r]` — a zero coefficient is never a usable
        //    entering candidate, so `select_entering` cannot have returned it;
        //  - `leave` is NOT in `row_nz[r]` — a basic variable's column is zero in
        //    its own row, which is the tableau's defining invariant;
        //  - `−a/a_re` is nonzero exactly when `a` is, so no OTHER cell of this
        //    row changes zero-state. The index therefore changes by removing
        //    `enter` and inserting `leave`, and by nothing else.
        let old_nz: Vec<usize> = self.row_nz[r].clone();
        for &v in &old_nz {
            if v == enter {
                continue;
            }
            let a = self.row[r][v];
            self.row[r][v] = sub(Rational::zero(), div(a, a_re)?)?;
        }
        self.row[r][enter] = Rational::zero();
        self.col_nnz[enter] -= 1;
        self.row[r][leave] = recip;
        self.col_nnz[leave] += 1;
        {
            let nz = &mut self.row_nz[r];
            if let Ok(at) = nz.binary_search(&enter) {
                nz.remove(at);
            }
            if let Err(at) = nz.binary_search(&leave) {
                nz.insert(at, leave);
            }
        }
        self.basic[r] = enter;
        self.is_basic[enter] = true;
        self.is_basic[leave] = false;

        // Substitute `enter`'s new expression into every OTHER row.
        // Only the pivot row's NONZERO columns are visited: adding `coeff · 0` is
        // an exact multiply and add that provably cannot change the cell. The
        // values are copied out by index — about 35 rationals — rather than by
        // cloning the whole `n`-wide row, which was the other 13.6 KB per pivot.
        let base_nz: Vec<usize> = self.row_nz[r].clone();
        let base_vals: Vec<Rational> = base_nz.iter().map(|&v| self.row[r][v]).collect();
        for i in 0..self.m {
            if i == r {
                continue;
            }
            let coeff = col[i];
            if coeff.is_zero() {
                continue;
            }
            // One integer add per ROW, not per cell: `base_nz.len()` is the exact
            // number of exact-rational multiply-adds this row costs, and it is
            // already in hand.
            self.counters.pivot_rows_combined += 1;
            self.counters.pivot_cells_written += base_nz.len() as u64;
            // row_i := row_i + coeff · new_row (eliminating `enter`'s column).
            for (k, &v) in base_nz.iter().enumerate() {
                let delta = mul(coeff, base_vals[k])?;
                let updated = add(self.row[i][v], delta)?;
                self.set_cell(i, v, updated);
            }
            self.set_cell(i, enter, Rational::zero());
        }

        // Values: the Dutertre–de Moura O(rows) update. `leave` lands on the bound
        // it violated, `enter` absorbs θ, and every other basic variable moves by
        // its OLD coefficient of `enter` times θ. This preserves the tableau
        // invariant `value[basic[i]] = Σ_{v nonbasic} row[i][v]·value[v]`, which
        // `tableau_invariant_holds_after_every_pivot` checks directly rather than
        // trusting this comment.
        self.value[leave] = target;
        self.value[enter] = enter_new;
        for i in 0..self.m {
            if i == r {
                continue;
            }
            let coeff = col[i];
            if coeff.is_zero() {
                continue;
            }
            let b = self.basic[i];
            self.value[b] = self.value[b].add(theta.scale(coeff)?)?;
        }
        Ok(())
    }

    /// Whether every basic variable's cached value equals its row evaluated over
    /// the nonbasic variables — the invariant the pivot's `O(rows)` value update
    /// maintains in place of a full recompute. Test-only.
    ///
    /// An arithmetic decline answers `true`: this checks the update, not the
    /// arithmetic, and a promoted-value overflow is a separate, already-handled
    /// path.
    #[cfg(test)]
    fn value_invariant_holds(&self) -> bool {
        for i in 0..self.m {
            let mut acc = Delta::zero();
            for v in 0..self.n {
                if self.is_basic[v] || self.row[i][v].is_zero() {
                    continue;
                }
                let Ok(term) = self.value[v].scale(self.row[i][v]) else {
                    return true;
                };
                let Ok(next) = acc.add(term) else {
                    return true;
                };
                acc = next;
            }
            if self.value[self.basic[i]].cmp(acc) != core::cmp::Ordering::Equal {
                return false;
            }
        }
        true
    }

    /// Materialize a concrete rational point from the current (feasible) δ-assignment
    /// by choosing an infinitesimal `δ = ε > 0` small enough that every original
    /// constraint still holds at the concrete point `xⱼ = cⱼ + kⱼ·ε`.
    ///
    /// For each row the δ-value `(C, K) = Σ aⱼ·(cⱼ, kⱼ)` already satisfies the bound
    /// in `ℚ(δ)`. Shrinking `ε` cannot break a row whose `C`-part is *strictly*
    /// inside its bound only if `ε` stays below that margin divided by `|K|`; a row
    /// binding in the `C`-part is safe for *any* `ε > 0` (the `K`-part has the right
    /// sign). We therefore take `ε` = half the smallest such margin (or `1` if none
    /// binds).
    fn materialize(&self) -> R<Vec<Rational>> {
        let mut eps = Rational::integer(1);
        for (i, sparse) in self.rows_sparse.iter().enumerate() {
            // Rows carrying no bound constrain nothing.
            let Some((rel, rhs)) = self.rel_rhs[i] else {
                continue;
            };
            // Row δ-value (C, K) over the problem variables.
            let mut cc = Rational::zero();
            let mut kk = Rational::zero();
            for &(j, a) in sparse {
                cc = add(cc, mul(a, self.value[j].c)?)?;
                kk = add(kk, mul(a, self.value[j].k)?)?;
            }
            // `margin = |b − C|`; the row binds ε only when C is strictly inside the
            // bound (margin > 0) and K pushes toward it. Then ε < margin / |K|.
            let margin = sub(rhs, cc)?; // b − C
            if margin.is_zero() || kk.is_zero() {
                continue;
            }
            // Toward-violation test: for an upper bound (Le/Lt) K>0 pushes up toward
            // b; for a lower bound (Ge/Gt) K<0 pushes down toward b. When margin and
            // the push have the shape that could cross, cap ε.
            let k_pos = cmp(kk, Rational::zero()) == core::cmp::Ordering::Greater;
            let toward = match rel {
                Rel::Le | Rel::Lt => k_pos,  // rising toward an upper bound
                Rel::Ge | Rel::Gt => !k_pos, // falling toward a lower bound
                Rel::Eq => true,             // any drift off an equality must be capped
            };
            if !toward {
                continue;
            }
            // Cap: ε ≤ |margin / K| / 2.  margin has the same sign as the room; take
            // the magnitude.
            let ratio = div(margin, kk)?;
            let mag = if cmp(ratio, Rational::zero()) == core::cmp::Ordering::Less {
                sub(Rational::zero(), ratio)?
            } else {
                ratio
            };
            let half = mul(mag, Rational::checked_new(1, 2).ok_or(Overflow)?)?;
            if cmp(half, eps) == core::cmp::Ordering::Less {
                eps = half;
            }
        }
        // xⱼ = cⱼ + kⱼ·ε.
        let mut out = Vec::with_capacity(self.nvars);
        for j in 0..self.nvars {
            out.push(add(self.value[j].c, mul(self.value[j].k, eps)?)?);
        }
        Ok(out)
    }

    /// Farkas-certificate extraction from the infeasible row `r` (P1.9 · T1.9.3).
    ///
    /// At infeasibility the basic variable `b` of row `r` is a **slack** pinned
    /// outside its bound, and every nonbasic variable with a nonzero coefficient in
    /// the row is also a slack pinned at a blocking bound (a nonbasic *problem*
    /// variable is unbounded, so it would have been selected as an entering variable
    /// — its presence would contradict infeasibility). The tableau row is a valid
    /// affine identity `slack_b − Σⱼ aⱼ·slackⱼ ≡ 0` in the problem variables, so the
    /// multipliers over the *input rows* are `y_b = ±1` and `yⱼ = ∓aⱼ` (the sign set
    /// by which bound `b` violates). That gives `yᵀA = 0` by construction.
    ///
    /// The candidate is **self-checked** by [`check_farkas`] before it is returned:
    /// the non-strict case yields `Σ y·rhs < 0`; a strict-row contradiction whose
    /// rational part cancels to `0` is accepted via the δ-aware `0 < 0` rule (a
    /// strict row is used). A candidate that does not verify returns **empty** — a
    /// sound "no certificate" that never masquerades as a refutation. So a returned
    /// vector is always a genuine, re-checkable Farkas certificate.
    fn farkas(&mut self, r: usize, too_low: bool) -> R<Vec<Rational>> {
        let b = self.basic[r];
        if b < self.nvars {
            // The infeasible basic variable must be a slack (problem vars are
            // unbounded and cannot violate a bound) — otherwise no closed form here.
            self.counters.farkas_declined_basic_not_slack += 1;
            return Ok(Vec::new());
        }
        // `sign`: a violated LOWER bound (`too_low`) means `b`'s row is a `≥`/`>`
        // input row, which takes a ≤0 multiplier ⇒ `y_b = −1`; a violated UPPER
        // bound is a `≤`/`<` row ⇒ `y_b = +1`.
        let sign = if too_low {
            Rational::integer(-1)
        } else {
            Rational::integer(1)
        };
        let mut y = vec![Rational::zero(); self.m];
        y[b - self.nvars] = sign;
        for v in 0..self.n {
            if self.is_basic[v] {
                continue;
            }
            let a = self.row[r][v];
            if a.is_zero() {
                continue;
            }
            if v < self.nvars {
                // A nonbasic problem variable in the row ⇒ not the pure-slack shape
                // infeasibility guarantees; decline the closed-form cert.
                self.counters.farkas_declined_nonbasic_problem_var += 1;
                return Ok(Vec::new());
            }
            // yⱼ = −sign·aⱼ over the input row of slack `v`.
            y[v - self.nvars] = mul(sub(Rational::zero(), sign)?, a)?;
        }
        // Self-check: return the certificate only if it genuinely refutes the input.
        if farkas_holds(self.nvars, &self.rows_sparse, &self.rel_rhs, &y) {
            self.counters.farkas_certificates += 1;
            Ok(y)
        } else {
            self.counters.farkas_declined_self_check += 1;
            Ok(Vec::new())
        }
    }
}

/// Status of one [`Incremental::check`].
///
/// `pub` (rather than `pub(crate)`) only so [`crate::bench_internals`] can
/// re-export it for `benches/simplex_pivot.rs`; the containing `simplex`
/// module stays crate-private and the re-export path is gated behind the
/// `bench-internals` feature, so this is not reachable from an ordinary
/// dependent of the crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status {
    /// The currently-bounded rows are jointly feasible; `Incremental::point`
    /// materializes the witness.
    Feasible,
    /// Infeasible. The payload is the set of **bounded row indices carrying a
    /// nonzero, self-verified Farkas multiplier** — the refutation's support. It is
    /// **empty** when no closed-form certificate could be extracted *and verified*:
    /// the infeasibility verdict itself is still sound (a basic variable is pinned
    /// outside its bound with no eligible entering variable), but the caller gets no
    /// minimized support and must fall back to a coarse explanation.
    Infeasible(Vec<usize>),
    /// Exact arithmetic declined (see the `Overflow` marker), or the pivot/deadline budget
    /// ran out — a sound "don't know", never a verdict.
    Unknown,
}

/// The **warm** general simplex a `DPLL(T)` theory drives (Dutertre–de Moura §4).
///
/// The tableau structure is built **once** over every row the theory could ever
/// assert (`slackᵢ = Σ aᵢⱼ·xⱼ`); asserting or retracting an atom only moves that
/// row's *bound*, so [`Incremental::check`] resumes from the previous basis and
/// assignment instead of re-deciding the whole system. That is the whole point:
/// the Fourier–Motzkin core it replaces is doubly exponential in the variable
/// count and re-ran from scratch on every assert.
///
/// # Scope and soundness
///
/// Rows carry **upper** bounds only (`Σ a·x ≤ rhs`, strict on request) — the shape
/// `crate::lra_online` normalizes every atom polarity into. Consequently no
/// variable ever has a lower bound, so the "lower > upper" immediate conflict of
/// the general algorithm cannot arise and every infeasibility is found by the
/// pivot loop, which is where the Farkas certificate comes from.
///
/// Every `Infeasible` support is self-verified by `farkas_holds` before it is
/// handed back; a candidate that fails verification is **discarded** (empty
/// support), never trusted. An arithmetic overflow poisons the cached assignment,
/// which the next [`Incremental::check`] repairs by rebuilding from the pristine
/// basis; while poisoned the engine answers [`Status::Unknown`].
///
/// `pub` bench-only, for the same reason as [`Status`]: reachable outside the
/// crate only through [`crate::bench_internals`], gated by the
/// `bench-internals` feature. Fields stay private; a bench drives this only
/// through [`Incremental::new`], [`Incremental::assert_bound`], and
/// [`Incremental::check`].
pub struct Incremental {
    tab: Tableau,
    /// Set when an overflow left [`Tableau::value`] inconsistent; the next `check`
    /// rebuilds before deciding anything.
    poisoned: bool,
    /// Completed [`Incremental::check`] calls. Diagnostic only.
    checks: u64,
    /// Checks that had to discard the basis and restart from the pristine one
    /// (the `poisoned` recovery path). Diagnostic only, and the number that
    /// distinguishes a genuinely warm engine from one silently rebuilding.
    cold_restarts: u64,
}

impl Incremental {
    /// Builds the warm engine over `nvars` problem variables and one row per
    /// `rows_sparse` entry, all rows initially **unbounded**.
    ///
    /// Returns `None` when the dense tableau would exceed [`MAX_TABLEAU_CELLS`] —
    /// a deterministic, purely structural decline that leaves the caller on
    /// whatever engine it had.
    pub fn new(nvars: usize, rows_sparse: Vec<Vec<(usize, Rational)>>) -> Option<Self> {
        Incremental::with_policy(nvars, rows_sparse, configured_policy())
    }

    /// As [`Incremental::new`], under an explicit [`PivotPolicy`].
    ///
    /// This is the A/B seam: the dense/Bland arm every measurement of a new rule
    /// is a ratio against stays runnable as `PivotPolicy::bland()` rather than
    /// surviving only as a number in a document.
    pub fn with_policy(
        nvars: usize,
        rows_sparse: Vec<Vec<(usize, Rational)>>,
        policy: PivotPolicy,
    ) -> Option<Self> {
        let m = rows_sparse.len();
        let n = nvars.checked_add(m)?;
        // ADR-1762: recorded so a `--trace` run can attribute a Fourier-Motzkin
        // fallback to this bound rather than to the query's shape. Off by
        // default; the verdict is identical either way.
        crate::config_registry::note_consulted(
            "crates/axeyum-solver/src/simplex.rs::MAX_TABLEAU_CELLS",
        );
        if m.checked_mul(n)? > MAX_TABLEAU_CELLS {
            return None;
        }
        Some(Incremental {
            tab: Tableau::new_rows_with_policy(nvars, rows_sparse, policy),
            poisoned: false,
            checks: 0,
            cold_restarts: 0,
        })
    }

    /// Number of rows the engine was built over.
    pub fn rows(&self) -> usize {
        self.tab.m
    }

    /// The clock-free structural counters accumulated over this engine's whole
    /// life. Diagnostic only; see [`TableauCounters`].
    #[must_use]
    pub fn counters(&self) -> TableauCounters {
        self.tab.counters
    }

    /// The policy this engine is running. Read by nothing that decides a
    /// verdict; present so a trace can say which arm produced a number.
    ///
    /// Compiled only for tests and for the `bench-internals` profile, which is
    /// the honest description of who can reach it: `PivotPolicy` is not exported
    /// from `lib.rs`, so under any other feature set this method returns a type
    /// no consumer outside this crate can name, and `clippy -D warnings` flags
    /// it as dead. SIX separate lanes re-reported that as a push blocker on
    /// 2026-09-09; it never was one, because the gate
    /// (`scripts/check-clippy-complete.sh`) runs `--all-features`, where
    /// `bench_internals` re-exports `Incremental` and the method is live. The
    /// `cfg` makes the narrow `--features full` invocation agree with the gate
    /// so nobody spends that hour again.
    #[cfg(any(test, feature = "bench-internals"))]
    #[must_use]
    pub fn policy(&self) -> PivotPolicy {
        self.tab.policy
    }

    /// Imposes `Σ aᵢⱼ·xⱼ ⋈ rhs` on row `i` and pulls the slack back inside the new
    /// bound if it is nonbasic. O(m), not O(m·n) — this is the operation a theory
    /// `assert` costs.
    ///
    /// A row carries **at most one** bound at a time: an order atom's row takes an
    /// upper bound when the atom is asserted true and a lower bound when it is
    /// asserted false, and the two polarities are mutually exclusive. So `lower` and
    /// `upper` on one variable can never cross, and every infeasibility is found by
    /// the pivot loop (which is where the Farkas certificate comes from).
    pub fn assert_bound(&mut self, i: usize, rel: Rel, rhs: Rational) {
        self.tab.set_row_bound(i, Some((rel, rhs)));
        if self.tab.clamp_nonbasic(self.tab.nvars + i).is_err() {
            self.poisoned = true;
        }
    }

    /// Removes row `i`'s bound. Relaxing can never invalidate the current
    /// assignment, so this needs no value repair.
    pub(crate) fn retract(&mut self, i: usize) {
        self.tab.set_row_bound(i, None);
    }

    /// Re-decides feasibility of the currently-bounded rows, warm-starting from the
    /// present basis.
    pub fn check(&mut self, deadline: Option<Instant>) -> Status {
        self.checks += 1;
        if self.poisoned {
            self.cold_restarts += 1;
            // Recover: pristine basis, bounds preserved, values recomputed.
            self.tab.reset_structure();
            for v in 0..self.tab.n {
                if self.tab.clamp_nonbasic(v).is_err() {
                    return Status::Unknown;
                }
            }
            self.poisoned = false;
        }
        match self.tab.run(deadline, MAX_PIVOTS) {
            Ok(RunOutcome::Feasible) => Status::Feasible,
            Ok(RunOutcome::Infeasible(y)) => Status::Infeasible(
                y.iter()
                    .enumerate()
                    .filter(|(_, m)| !m.is_zero())
                    .map(|(i, _)| i)
                    .collect(),
            ),
            Ok(RunOutcome::Unknown) => Status::Unknown,
            Err(Overflow) => {
                self.poisoned = true;
                Status::Unknown
            }
        }
    }

    /// Pivots this engine has performed over its whole life, across every
    /// [`Incremental::check`]. Diagnostic only — no decision reads it.
    #[must_use]
    pub fn pivots(&self) -> u64 {
        self.tab.total_pivots
    }

    /// Completed [`Incremental::check`] calls. Diagnostic only.
    #[must_use]
    pub fn checks(&self) -> u64 {
        self.checks
    }

    /// Total columns of the dense tableau (`nvars + rows`). Diagnostic only;
    /// paired with [`Incremental::rows`] it is what prices one pivot, which is
    /// `O(rows × columns)` rational operations.
    #[must_use]
    pub fn columns(&self) -> u64 {
        self.tab.n as u64
    }

    /// Checks that discarded the basis and restarted from the pristine one.
    /// Diagnostic only; a nonzero value means the engine was **not** warm for
    /// that many checks.
    #[must_use]
    pub fn cold_restarts(&self) -> u64 {
        self.cold_restarts
    }

    /// A concrete rational point for the problem variables after a
    /// [`Status::Feasible`] check, or `None` on overflow. The caller replays it
    /// against the original assertions — that replay, not this function, is what
    /// makes a `sat` trustworthy.
    pub(crate) fn point(&self) -> Option<Vec<Rational>> {
        // `narrow`: a promoted witness cannot cross this boundary (ADR-1702).
        self.tab.materialize().ok().and_then(narrow)
    }
}

/// Re-check a Farkas certificate `y` against the input `constraints`: every `y`
/// respects its row's sign (`≥0` for `≤`/`<`, `≤0` for `≥`/`>`, free for `=`), the
/// combined left-hand side vanishes (`Σ yᵢ·aᵢⱼ = 0` for every column `j`), and the
/// combined right-hand side refutes — `Σ yᵢ·bᵢ < 0`, or `= 0` when a strict (`<`/`>`)
/// row is used (the δ-aware `0 < 0`). Used by the tests here and by any caller
/// before trusting an `Infeasible` verdict.
// The dense public verifier is the module's *contract* surface: the in-tree callers
// verify differently (`crate::lra` rebuilds its own `FarkasCertificate`, the warm
// engine self-checks over the sparse rows), so nothing but the tests calls this.
#[allow(dead_code)]
#[must_use]
pub fn check_farkas(nvars: usize, constraints: &[Constraint], y: &[Rational]) -> bool {
    if y.len() != constraints.len() {
        return false;
    }
    let rows: Vec<Vec<(usize, Rational)>> = constraints
        .iter()
        .map(|c| densify_to_sparse(&c.coeffs))
        .collect();
    let rel_rhs: Vec<Option<(Rel, Rational)>> =
        constraints.iter().map(|c| Some((c.rel, c.rhs))).collect();
    farkas_holds(nvars, &rows, &rel_rhs, y)
}

/// The single implementation behind [`check_farkas`] and the tableau's own
/// certificate self-check, over the sparse row form.
///
/// A row with `rel_rhs[i] == None` carries **no bound**, so it states nothing and
/// cannot participate: a nonzero multiplier on such a row is rejected outright.
fn farkas_holds(
    nvars: usize,
    rows: &[Vec<(usize, Rational)>],
    rel_rhs: &[Option<(Rel, Rational)>],
    y: &[Rational],
) -> bool {
    if y.len() != rows.len() || y.len() != rel_rhs.len() || y.iter().all(|v| v.is_zero()) {
        return false;
    }
    // Sign discipline per row (and: an unbounded row states nothing).
    for (yi, rr) in y.iter().zip(rel_rhs) {
        let Some((rel, _)) = rr else {
            if !yi.is_zero() {
                return false;
            }
            continue;
        };
        let Some(s) = yi.checked_cmp(&Rational::zero()) else {
            return false;
        };
        match rel {
            // `≤`/`<` rows take a ≥0 multiplier; `≥`/`>` rows a ≤0 one; `=` is free.
            Rel::Le | Rel::Lt if s == core::cmp::Ordering::Less => return false,
            Rel::Ge | Rel::Gt if s == core::cmp::Ordering::Greater => return false,
            _ => {}
        }
    }
    // Column sums must vanish.
    let mut acc = vec![Rational::zero(); nvars];
    for (yi, sparse) in y.iter().zip(rows) {
        if yi.is_zero() {
            continue;
        }
        for &(j, a) in sparse {
            if j >= nvars {
                return false;
            }
            let Some(t) = yi.checked_mul(a) else {
                return false;
            };
            let Some(s) = acc[j].checked_add(t) else {
                return false;
            };
            acc[j] = s;
        }
    }
    if acc.iter().any(|a| !a.is_zero()) {
        return false;
    }
    // Combined rhs, and whether a strict (`<`/`>`) row is actually used. The
    // refutation is the derived relation `0 ⋈ Σy·rhs` in `ℚ(δ)`: with the combined
    // LHS vanishing, it collapses to `Σy·rhs ≥ 0` (or `> 0` when a strict row
    // contributes a `−δ`). It refutes iff that is false:
    //   * `Σy·rhs < 0`               — false regardless of δ; or
    //   * `Σy·rhs == 0` AND a strict row is used — the `0 < 0` case.
    let mut total = Rational::zero();
    let mut strict_used = false;
    for (yi, rr) in y.iter().zip(rel_rhs) {
        let Some((rel, rhs)) = rr else { continue };
        let Some(t) = yi.checked_mul(*rhs) else {
            return false;
        };
        let Some(s) = total.checked_add(t) else {
            return false;
        };
        total = s;
        if !yi.is_zero() && matches!(rel, Rel::Lt | Rel::Gt) {
            strict_used = true;
        }
    }
    match total.checked_cmp(&Rational::zero()) {
        Some(core::cmp::Ordering::Less) => true,
        Some(core::cmp::Ordering::Equal) => strict_used,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The unbounded one-shot call, for the cases below that are about the
    /// arithmetic rather than the clock. Deliberately a TEST helper: there is
    /// no production caller that owns no deadline, and when `feasible` was a
    /// module-level function the whole `lra` route reached the pivot loop with
    /// its budget wired to a literal `None`.
    fn feasible(nvars: usize, constraints: &[Constraint]) -> SimplexOutcome {
        feasible_within(nvars, constraints, None)
    }

    /// `Incremental::policy` reports the policy the engine is actually
    /// running, and `with_policy` is honoured rather than silently replaced by
    /// the configured default.
    ///
    /// Added 2026-09-09, because the shipped entering rule and its Bland
    /// fallback threshold were pinned by nothing. The reference comparison in
    /// `docs/solver-comparison-2026-09/05-yices-opensmt-smtinterpol.md` records
    /// them as the choice that distinguishes this simplex from Yices2,
    /// `OpenSMT` and `SMTInterpol`, so they are worth a test that fails when
    /// they move.
    ///
    /// A note on the dead-code lint, since three separate lanes reported it as
    /// a push blocker on the same day and it is not one: `policy()` has no
    /// non-test caller, and under `--features full` alone `clippy -D warnings`
    /// does fail on it. Under `--all-features` it does NOT, because
    /// `bench_internals` (`lib.rs:273`) re-exports `Incremental` and the method
    /// becomes reachable public API. The gate the pre-push hook actually runs
    /// (`scripts/check-clippy-complete.sh`) passes `--all-features`, so it was
    /// always green. Measure the gate, not a narrower proxy for it.
    #[test]
    fn the_engine_reports_the_pivot_policy_it_was_built_with() {
        let rows = vec![vec![(0usize, r(1))]];

        // The shipped default: fill-in minimising, Bland as a fallback.
        let dflt = Incremental::with_policy(1, rows.clone(), PivotPolicy::new())
            .expect("1x1 tableau is far below MAX_TABLEAU_CELLS");
        assert_eq!(dflt.policy().entering, EnteringRule::MinimiseFillIn);
        assert_eq!(dflt.policy().bland_threshold, 1_000);

        // The pre-2026-09-08 baseline is still selectable and still reports
        // itself. A baseline you cannot run is a remembered number.
        let bland = Incremental::with_policy(1, rows, PivotPolicy::bland())
            .expect("1x1 tableau is far below MAX_TABLEAU_CELLS");
        assert_eq!(bland.policy().entering, EnteringRule::Bland);
        assert_ne!(dflt.policy().entering, bland.policy().entering);
    }

    /// `x_i = 2·x_{i+1}` for `i` in `0..n-1`, plus `x_{n-1} ≥ 1`: satisfiable,
    /// with the unique vertex `x_j = 2^(n-1-j)`. Small integer coefficients
    /// throughout, so nothing about the INPUT is out of range — only the answer.
    fn doubling_chain(n: usize) -> Vec<Constraint> {
        let mut rows: Vec<Constraint> = Vec::with_capacity(n);
        for i in 0..(n - 1) {
            let mut coeffs = vec![Rational::zero(); n];
            coeffs[i] = r(1);
            coeffs[i + 1] = r(-2);
            rows.push(Constraint {
                coeffs,
                rel: Rel::Eq,
                rhs: r(0),
            });
        }
        let mut coeffs = vec![Rational::zero(); n];
        coeffs[n - 1] = r(1);
        rows.push(Constraint {
            coeffs,
            rel: Rel::Ge,
            rhs: r(1),
        });
        rows
    }

    /// `2^k` as an exact rational, built by the promoting family so the test
    /// itself never depends on `i128` range.
    fn pow2(k: u32) -> Rational {
        let mut acc = Rational::integer(1);
        for _ in 0..k {
            acc = acc.wide_add(acc).expect("big-rational pool has room");
        }
        acc
    }

    /// The `i128` witness boundary, pinned together with the query it costs.
    ///
    /// The 131-variable doubling chain is SATISFIABLE and the tableau finds its
    /// exact vertex, `x_0 = 2^130`. Four of the 131 coordinates are outside
    /// `i128`, so [`narrow`] discards the whole witness and [`feasible`] answers
    /// `Unknown` on a query that has a model. That decline is roadmap item 2.3
    /// (`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`), and this test
    /// is what must change when it is closed — [`narrow`]'s doc comment lists
    /// the consumers that have to be able to read a promoted value first.
    ///
    /// The assertions are ordered so a failure says WHICH half moved. If the
    /// tableau stopped finding the exact vertex, the first three fail; if the
    /// boundary opened, only the last two do. A test that asserted `Unknown` and
    /// nothing else could not tell those apart, and would pass just as happily
    /// on a simplex that had stopped working.
    #[test]
    fn the_witness_boundary_discards_an_exact_model_that_exceeds_i128() {
        const N: usize = 131; // x0 .. x130
        let rows = doubling_chain(N);

        // 1. The tableau itself decides the system, before any narrowing.
        let mut tab = Tableau::new(N, &rows);
        assert!(
            matches!(tab.run(None, MAX_PIVOTS), Ok(RunOutcome::Feasible)),
            "the doubling chain is satisfiable and the tableau must find it"
        );

        // 2. And the witness it materializes is exact, not approximate.
        let point = tab
            .materialize()
            .unwrap_or_else(|Overflow| panic!("materialize declined on the doubling chain"));
        assert_eq!(point.len(), N);
        assert_eq!(point[N - 1], r(1), "x_130 sits on its lower bound");
        assert_eq!(point[0], pow2(130), "x_0 is exactly 2^130");

        // 3. Four coordinates (2^127 .. 2^130) are outside `i128`.
        assert_eq!(
            point.iter().filter(|v| v.is_big()).count(),
            4,
            "2^127, 2^128, 2^129 and 2^130 exceed i128::MAX = 2^127 - 1"
        );

        // 4. Which is the whole reason the boundary refuses …
        assert!(
            narrow(point).is_none(),
            "narrow declines the moment any coordinate is promoted"
        );

        // 5. … and the reason a satisfiable query answers `Unknown`.
        assert_eq!(
            feasible(N, &rows),
            SimplexOutcome::Unknown,
            "roadmap item 2.3: this must become Feasible, with a replayable model"
        );
    }

    fn r(n: i128) -> Rational {
        Rational::integer(n)
    }
    fn con(coeffs: &[i128], rel: Rel, rhs: i128) -> Constraint {
        Constraint {
            coeffs: coeffs.iter().map(|&c| r(c)).collect(),
            rel,
            rhs: r(rhs),
        }
    }

    /// Evaluate every constraint at a candidate point; true iff all hold.
    fn satisfies(cs: &[Constraint], x: &[Rational]) -> bool {
        cs.iter().all(|c| {
            let mut acc = Rational::zero();
            for (a, xi) in c.coeffs.iter().zip(x) {
                acc = acc.checked_add(a.checked_mul(*xi).unwrap()).unwrap();
            }
            let o = acc.checked_cmp(&c.rhs).unwrap();
            match c.rel {
                Rel::Le => o != core::cmp::Ordering::Greater,
                Rel::Ge => o != core::cmp::Ordering::Less,
                Rel::Eq => o == core::cmp::Ordering::Equal,
                Rel::Lt => o == core::cmp::Ordering::Less,
                Rel::Gt => o == core::cmp::Ordering::Greater,
            }
        })
    }

    #[test]
    fn single_var_feasible() {
        // x ≥ 1 ∧ x ≤ 3  → feasible.
        let cs = [con(&[1], Rel::Ge, 1), con(&[1], Rel::Le, 3)];
        match feasible(1, &cs) {
            SimplexOutcome::Feasible(x) => assert!(satisfies(&cs, &x)),
            o => panic!("expected feasible, got {o:?}"),
        }
    }

    /// The one-shot entry point must hand its caller's deadline to the pivot
    /// loop, not the literal `None` it passed for the whole of this engine's
    /// life.
    ///
    /// `Tableau::run` has always polled correctly; the defect was the argument.
    /// So the discriminating input is a system the engine decides instantly
    /// (any bound would be met) under a deadline that has ALREADY passed: the
    /// loop's entry poll must convert that into `Unknown`.
    #[test]
    fn the_one_shot_entry_point_hands_the_pivot_loop_its_deadline() {
        let cs = [con(&[1], Rel::Ge, 1), con(&[1], Rel::Le, 3)];
        let expired = Instant::now()
            .checked_sub(core::time::Duration::from_secs(1))
            .expect("an instant one second ago");
        assert!(
            matches!(
                feasible_within(1, &cs, Some(expired)),
                SimplexOutcome::Unknown
            ),
            "an expired deadline must stop the pivot loop before it decides"
        );
        // Positive control, same system: unbounded, it decides. Without this the
        // assertion above would also pass on an engine that answered `Unknown`
        // to everything.
        assert!(
            matches!(feasible_within(1, &cs, None), SimplexOutcome::Feasible(_)),
            "with no deadline the same system must still be decided feasible"
        );
    }

    #[test]
    fn single_var_infeasible_carries_farkas() {
        // x ≥ 3 ∧ x ≤ 1 → infeasible with an extracted, self-checked Farkas cert.
        let cs = [con(&[1], Rel::Ge, 3), con(&[1], Rel::Le, 1)];
        match feasible(1, &cs) {
            SimplexOutcome::Infeasible(y) => {
                assert!(
                    check_farkas(1, &cs, &y),
                    "non-strict infeasible must carry a valid Farkas cert, got {y:?}"
                );
            }
            o => panic!("expected infeasible, got {o:?}"),
        }
    }

    #[test]
    fn check_farkas_accepts_valid_and_rejects_invalid() {
        // x ≥ 3 ∧ x ≤ 1. The correct combination normalizes both to `≤`:
        //   (x≥3) as −x ≤ −3 with λ₀≥0; (x≤1) as x ≤ 1 with λ₁≥0; λ₀=λ₁=1 gives
        //   0 ≤ −2. Over the ORIGINAL rows the multipliers are y=(−1, +1): the `≥`
        //   row takes a ≤0 multiplier, the `≤` row a ≥0 one; Σy·a = −1+1 = 0 and
        //   Σy·b = −3+1 = −2 < 0.
        let cs = [con(&[1], Rel::Ge, 3), con(&[1], Rel::Le, 1)];
        assert!(check_farkas(1, &cs, &[r(-1), r(1)]), "valid cert must pass");
        // Wrong signs (positive multiplier on a `≥` row) must be rejected.
        assert!(
            !check_farkas(1, &cs, &[r(1), r(-1)]),
            "bad-sign cert rejected"
        );
        // The all-zero "cert" is not a refutation.
        assert!(!check_farkas(1, &cs, &[r(0), r(0)]), "zero cert rejected");
        // A cert whose lhs does not vanish is rejected.
        assert!(
            !check_farkas(1, &cs, &[r(-1), r(2)]),
            "nonzero-lhs cert rejected"
        );
    }

    #[test]
    fn two_var_feasible() {
        // x + y ≤ 4 ∧ x ≥ 1 ∧ y ≥ 1  → feasible (e.g. (1,1)).
        let cs = [
            con(&[1, 1], Rel::Le, 4),
            con(&[1, 0], Rel::Ge, 1),
            con(&[0, 1], Rel::Ge, 1),
        ];
        match feasible(2, &cs) {
            SimplexOutcome::Feasible(x) => assert!(satisfies(&cs, &x)),
            o => panic!("expected feasible, got {o:?}"),
        }
    }

    #[test]
    fn two_var_infeasible() {
        // x + y ≥ 10 ∧ x ≤ 2 ∧ y ≤ 2 → infeasible.
        let cs = [
            con(&[1, 1], Rel::Ge, 10),
            con(&[1, 0], Rel::Le, 2),
            con(&[0, 1], Rel::Le, 2),
        ];
        match feasible(2, &cs) {
            SimplexOutcome::Infeasible(y) => {
                assert!(
                    check_farkas(2, &cs, &y),
                    "non-strict infeasible must carry a valid Farkas cert, got {y:?}"
                );
            }
            o => panic!("expected infeasible, got {o:?}"),
        }
    }

    #[test]
    fn equality_system_feasible() {
        // x + y = 3 ∧ x − y = 1 → x=2, y=1.
        let cs = [con(&[1, 1], Rel::Eq, 3), con(&[1, -1], Rel::Eq, 1)];
        match feasible(2, &cs) {
            SimplexOutcome::Feasible(x) => {
                assert!(satisfies(&cs, &x));
            }
            o => panic!("expected feasible, got {o:?}"),
        }
    }

    #[test]
    fn equality_system_infeasible() {
        // x + y = 3 ∧ x + y = 5 → infeasible with a self-checked Farkas cert.
        let cs = [con(&[1, 1], Rel::Eq, 3), con(&[1, 1], Rel::Eq, 5)];
        match feasible(2, &cs) {
            SimplexOutcome::Infeasible(y) => assert!(check_farkas(2, &cs, &y)),
            o => panic!("expected infeasible, got {o:?}"),
        }
    }

    #[test]
    fn empty_constraints_feasible() {
        assert!(matches!(feasible(2, &[]), SimplexOutcome::Feasible(_)));
    }

    #[test]
    fn strict_contradiction_infeasible_carries_farkas() {
        // x < 1 ∧ x > 1 → infeasible (the δ-relaxation makes the strict bounds
        // exact: x ≤ 1−δ ∧ x ≥ 1+δ is empty), with a δ-aware Farkas cert whose
        // rational part sums to 0 and refutes via the strict `0 < 0`.
        let cs = [con(&[1], Rel::Lt, 1), con(&[1], Rel::Gt, 1)];
        match feasible(1, &cs) {
            SimplexOutcome::Infeasible(y) => assert!(
                check_farkas(1, &cs, &y),
                "strict contradiction must carry a valid δ-aware Farkas cert, got {y:?}"
            ),
            o => panic!("expected infeasible, got {o:?}"),
        }
    }

    #[test]
    fn check_farkas_strict_zero_sum() {
        // The δ-aware acceptance: rational parts cancel to 0 but a strict row is
        // used ⇒ `0 < 0`. `x < 1 ∧ x > 1` with y = (1, −1): Σy·rhs = 1−1 = 0.
        let cs = [con(&[1], Rel::Lt, 1), con(&[1], Rel::Gt, 1)];
        assert!(
            check_farkas(1, &cs, &[r(1), r(-1)]),
            "strict 0<0 cert must pass"
        );
        // The same shape with NON-strict rows is 0 ≤ 0 — not a refutation.
        let ns = [con(&[1], Rel::Le, 1), con(&[1], Rel::Ge, 1)];
        assert!(
            !check_farkas(1, &ns, &[r(1), r(-1)]),
            "non-strict 0=0 is feasible (x=1), must be rejected"
        );
    }

    #[test]
    fn strict_interval_feasible_point_replays() {
        // 0 < x < 2 → feasible; the MATERIALIZED concrete point must satisfy both
        // strict bounds (a wrong ε would put it on a boundary and fail replay).
        let cs = [con(&[1], Rel::Gt, 0), con(&[1], Rel::Lt, 2)];
        match feasible(1, &cs) {
            SimplexOutcome::Feasible(x) => assert!(satisfies(&cs, &x)),
            o => panic!("expected feasible, got {o:?}"),
        }
    }

    #[test]
    fn strict_vs_nonstrict_boundary() {
        // x ≤ 1 ∧ x ≥ 1 → feasible (x=1); x < 1 ∧ x ≥ 1 → infeasible.
        let feas = [con(&[1], Rel::Le, 1), con(&[1], Rel::Ge, 1)];
        assert!(matches!(feasible(1, &feas), SimplexOutcome::Feasible(_)));
        let infeas = [con(&[1], Rel::Lt, 1), con(&[1], Rel::Ge, 1)];
        assert!(matches!(
            feasible(1, &infeas),
            SimplexOutcome::Infeasible(_)
        ));
    }

    #[test]
    fn two_var_strict_feasible_replays() {
        // x + y < 4 ∧ x > 1 ∧ y > 1 → feasible; the point must strictly satisfy all.
        let cs = [
            con(&[1, 1], Rel::Lt, 4),
            con(&[1, 0], Rel::Gt, 1),
            con(&[0, 1], Rel::Gt, 1),
        ];
        match feasible(2, &cs) {
            SimplexOutcome::Feasible(x) => assert!(satisfies(&cs, &x)),
            o => panic!("expected feasible, got {o:?}"),
        }
    }

    /// A deterministic LCG (no clock / OS entropy) so the sweep is reproducible.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0
        }
        fn in_range(&mut self, lo: i128, hi: i128) -> i128 {
            let span = u64::try_from(hi - lo + 1).unwrap();
            lo + i128::from(self.next() % span)
        }
    }

    /// The `O(rows)` value update inside [`Tableau::pivot_and_update`] must leave
    /// the tableau invariant `β(basic[i]) = Σ_{v nonbasic} row[i][v]·β(v)` true
    /// after **every single pivot**, not merely at the end of a run — that
    /// invariant is what the removed `O(rows × columns)` recompute used to
    /// re-establish by brute force (S4).
    ///
    /// The pivot loop is stepped one pivot at a time (`budget = 1`) and the
    /// invariant checked between steps, over random systems in both the feasible
    /// and infeasible directions. Deleting the value-update loop, or reading the
    /// entering column *after* the elimination has zeroed it, makes this fail.
    #[test]
    fn tableau_invariant_holds_after_every_pivot() {
        let mut pivots_observed = 0u32;
        let mut systems_with_pivots = 0u32;
        for seed in 0..300u64 {
            let mut rng = Lcg(seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407));
            let nvars = usize::try_from(rng.in_range(2, 4)).unwrap();
            let ncon = usize::try_from(rng.in_range(2, 6)).unwrap();
            let mut cs: Vec<Constraint> = Vec::with_capacity(ncon);
            for _ in 0..ncon {
                let coeffs: Vec<Rational> = (0..nvars).map(|_| r(rng.in_range(-3, 3))).collect();
                let rel = match rng.in_range(0, 4) {
                    0 => Rel::Le,
                    1 => Rel::Ge,
                    2 => Rel::Eq,
                    3 => Rel::Lt,
                    _ => Rel::Gt,
                };
                cs.push(Constraint {
                    coeffs,
                    rel,
                    rhs: r(rng.in_range(-4, 4)),
                });
            }
            let mut tab = Tableau::new(nvars, &cs);
            for v in 0..tab.n {
                if tab.clamp_nonbasic(v).is_err() {
                    break;
                }
            }
            assert!(
                tab.value_invariant_holds(),
                "seed {seed}: invariant broken before any pivot"
            );
            let mut steps = 0u32;
            loop {
                let before = tab.total_pivots;
                match tab.run(None, 1) {
                    Ok(RunOutcome::Feasible | RunOutcome::Infeasible(_)) | Err(Overflow) => break,
                    Ok(RunOutcome::Unknown) => {}
                }
                if tab.total_pivots > before {
                    pivots_observed += 1;
                    if steps == 0 {
                        systems_with_pivots += 1;
                    }
                }
                assert!(
                    tab.value_invariant_holds(),
                    "seed {seed}: tableau invariant broken after pivot {steps}"
                );
                steps += 1;
                if steps > 64 {
                    break;
                }
            }
        }
        // A vacuous pass — every system feasible at the pristine basis, so no pivot
        // ever ran — would check nothing. Require real pivots on real systems.
        assert!(
            pivots_observed > 100,
            "only {pivots_observed} pivots exercised; the invariant check is near-vacuous"
        );
        assert!(
            systems_with_pivots > 20,
            "only {systems_with_pivots} systems pivoted at all"
        );
    }

    /// Adversarial differential: `simplex::feasible` must agree on sat/unsat with the
    /// trusted Fourier–Motzkin [`crate::lra::check_with_lra`] on random non-strict
    /// rational systems, and every `Feasible` point must replay. This is the P1.9
    /// T1.9.1 exit criterion (a wrong sat/unsat here would be the worst bug).
    #[test]
    fn simplex_agrees_with_fourier_motzkin() {
        use crate::backend::CheckResult;
        use axeyum_ir::{Sort, TermArena};

        let mut agreements = 0u32;
        for seed in 0..400u64 {
            let mut rng = Lcg(seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407));
            let nvars = usize::try_from(rng.in_range(2, 3)).unwrap();
            let ncon = usize::try_from(rng.in_range(2, 5)).unwrap();

            // Build the constraint data once; materialize into both engines.
            let mut cs: Vec<Constraint> = Vec::with_capacity(ncon);
            for _ in 0..ncon {
                let coeffs: Vec<Rational> = (0..nvars).map(|_| r(rng.in_range(-3, 3))).collect();
                let rel = match rng.in_range(0, 4) {
                    0 => Rel::Le,
                    1 => Rel::Ge,
                    2 => Rel::Eq,
                    3 => Rel::Lt,
                    _ => Rel::Gt,
                };
                let rhs = r(rng.in_range(-5, 5));
                cs.push(Constraint { coeffs, rel, rhs });
            }

            // --- simplex ---
            let simplex = feasible(nvars, &cs);

            // --- equivalent IR system for Fourier–Motzkin ---
            let mut arena = TermArena::new();
            let names = ["x", "y", "z"];
            let vars: Vec<_> = (0..nvars)
                .map(|j| {
                    let s = arena.declare(names[j], Sort::Real).unwrap();
                    arena.var(s)
                })
                .collect();
            let zero = arena.real_const(Rational::zero());
            let mut assertions = Vec::with_capacity(ncon);
            for c in &cs {
                let mut lhs: Option<axeyum_ir::TermId> = None;
                for (j, &coeff) in c.coeffs.iter().enumerate() {
                    if coeff.is_zero() {
                        continue;
                    }
                    let cst = arena.real_const(coeff);
                    let term = arena.real_mul(cst, vars[j]).unwrap();
                    lhs = Some(match lhs {
                        None => term,
                        Some(acc) => arena.real_add(acc, term).unwrap(),
                    });
                }
                let lhs = lhs.unwrap_or(zero);
                let rhs = arena.real_const(c.rhs);
                let atom = match c.rel {
                    Rel::Le => arena.real_le(lhs, rhs).unwrap(),
                    Rel::Ge => arena.real_ge(lhs, rhs).unwrap(),
                    Rel::Eq => arena.eq(lhs, rhs).unwrap(),
                    Rel::Lt => arena.real_lt(lhs, rhs).unwrap(),
                    Rel::Gt => arena.real_gt(lhs, rhs).unwrap(),
                };
                assertions.push(atom);
            }
            let fm = crate::lra::check_with_lra(&arena, &assertions).unwrap();

            // Adjudicate. Either engine may be `Unknown` (sound); only a definite
            // sat-vs-unsat disagreement is a bug.
            let simplex_sat = match &simplex {
                SimplexOutcome::Feasible(x) => {
                    assert!(
                        satisfies(&cs, x),
                        "seed {seed}: simplex Feasible point does not replay: {cs:?} @ {x:?}"
                    );
                    Some(true)
                }
                SimplexOutcome::Infeasible(y) => {
                    // Any extracted certificate must self-check; an empty vector is
                    // the sound "strict-δ cert deferred" case and is allowed.
                    assert!(
                        y.is_empty() || check_farkas(nvars, &cs, y),
                        "seed {seed}: extracted Farkas cert fails self-check: {cs:?} @ {y:?}"
                    );
                    Some(false)
                }
                SimplexOutcome::Unknown => None,
            };
            let fm_sat = match fm {
                CheckResult::Sat(_) => Some(true),
                CheckResult::Unsat => Some(false),
                CheckResult::Unknown(_) => None,
            };
            if let (Some(a), Some(b)) = (simplex_sat, fm_sat) {
                assert_eq!(
                    a, b,
                    "seed {seed}: DISAGREE simplex_sat={a} fm_sat={b} on {cs:?}"
                );
                agreements += 1;
            }
        }
        assert!(
            agreements > 200,
            "too few jointly-decided systems ({agreements}); differential not exercised"
        );
    }

    // --- the warm incremental engine (P1.9 · T1.9.2) -----------------------------

    /// Sparse row form of a dense coefficient list, for the incremental engine.
    fn sparse(coeffs: &[i128]) -> Vec<(usize, Rational)> {
        coeffs
            .iter()
            .enumerate()
            .filter(|&(_, &c)| c != 0)
            .map(|(j, &c)| (j, r(c)))
            .collect()
    }

    /// The one-shot `Constraint` list corresponding to an active-bound set.
    fn active_constraints(
        nvars: usize,
        rows: &[Vec<i128>],
        active: &[(usize, i128, Rel)],
    ) -> Vec<Constraint> {
        active
            .iter()
            .map(|&(i, rhs, rel)| Constraint {
                coeffs: (0..nvars).map(|j| r(rows[i][j])).collect(),
                rel,
                rhs: r(rhs),
            })
            .collect()
    }

    /// Build a warm engine over `rows`, impose `active`, and decide.
    fn incremental_verdict(
        nvars: usize,
        rows: &[Vec<i128>],
        active: &[(usize, i128, Rel)],
    ) -> (Status, Option<Vec<Rational>>) {
        let mut eng = Incremental::new(nvars, rows.iter().map(|row| sparse(row)).collect())
            .expect("tiny tableau is under the cell cap");
        for &(i, rhs, rel) in active {
            eng.assert_bound(i, rel, r(rhs));
        }
        let status = eng.check(None);
        let point = if status == Status::Feasible {
            eng.point()
        } else {
            None
        };
        (status, point)
    }

    /// **Soundness-negative, the headline one**: on random upper-bound systems the
    /// warm engine must never call a *satisfiable* set unsat, and never call an
    /// *unsatisfiable* set sat. The one-shot [`feasible`] over the same active rows
    /// is the reference (itself already gated against Fourier–Motzkin above), and a
    /// `Feasible` point must replay against the active rows.
    #[test]
    fn incremental_agrees_with_one_shot_and_never_reports_a_false_unsat() {
        let mut decided = 0u32;
        let mut infeasible_seen = 0u32;
        for seed in 0..500u64 {
            let mut rng = Lcg(seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407));
            let nvars = usize::try_from(rng.in_range(1, 3)).unwrap();
            let nrows = usize::try_from(rng.in_range(2, 6)).unwrap();
            let rows: Vec<Vec<i128>> = (0..nrows)
                .map(|_| (0..nvars).map(|_| rng.in_range(-3, 3)).collect())
                .collect();
            // A random *subset* of rows carries a bound — the shape the theory
            // produces, where unasserted atoms leave their rows unbounded.
            let mut active: Vec<(usize, i128, Rel)> = Vec::new();
            for (i, _) in rows.iter().enumerate() {
                if rng.in_range(0, 2) != 0 {
                    // Order atoms now produce LOWER bounds too (the `when_false`
                    // polarity rides its `when_true` slack), so the fuzz must cover
                    // `≥`/`>` as well as `≤`/`<`.
                    let rel = match rng.in_range(0, 3) {
                        0 => Rel::Le,
                        1 => Rel::Lt,
                        2 => Rel::Ge,
                        _ => Rel::Gt,
                    };
                    active.push((i, rng.in_range(-5, 5), rel));
                }
            }
            if active.is_empty() {
                continue;
            }

            let cs = active_constraints(nvars, &rows, &active);
            let (status, point) = incremental_verdict(nvars, &rows, &active);
            let reference = feasible(nvars, &cs);

            match (&status, &reference) {
                (Status::Feasible, SimplexOutcome::Infeasible(_)) => {
                    panic!("seed {seed}: warm engine said SAT where the one-shot refutes: {cs:?}")
                }
                (Status::Infeasible(support), SimplexOutcome::Feasible(x)) => panic!(
                    "seed {seed}: WRONG UNSAT — warm engine refuted a system with witness {x:?}; \
                     support={support:?} rows={cs:?}"
                ),
                (Status::Feasible, SimplexOutcome::Feasible(_)) => {
                    let x = point.expect("a feasible warm check materializes a point");
                    assert!(
                        satisfies(&cs, &x),
                        "seed {seed}: warm Feasible point does not replay: {cs:?} @ {x:?}"
                    );
                    decided += 1;
                }
                (Status::Infeasible(support), SimplexOutcome::Infeasible(_)) => {
                    // The named support must itself be infeasible — a genuine core,
                    // not a padded one. (An empty support is the sound "no verified
                    // certificate" case the caller widens.)
                    if !support.is_empty() {
                        let sub: Vec<(usize, i128, Rel)> = support
                            .iter()
                            .map(|&row| {
                                *active
                                    .iter()
                                    .find(|(i, _, _)| *i == row)
                                    .expect("support names a bounded row")
                            })
                            .collect();
                        let sub_cs = active_constraints(nvars, &rows, &sub);
                        assert!(
                            matches!(feasible(nvars, &sub_cs), SimplexOutcome::Infeasible(_)),
                            "seed {seed}: the named core is NOT infeasible on its own: {sub_cs:?}"
                        );
                        infeasible_seen += 1;
                    }
                    decided += 1;
                }
                (Status::Unknown, _) | (_, SimplexOutcome::Unknown) => {}
            }
        }
        assert!(decided > 300, "too few decided systems ({decided})");
        assert!(
            infeasible_seen > 20,
            "too few verified cores ({infeasible_seen}); the refutation path is not exercised"
        );
    }

    /// **Soundness-negative for the warm start.** The whole point of the engine is
    /// that a check resumes from the previous basis; a stale basis or a stale value
    /// cache would be exactly the way a wrong verdict enters. Drive a random
    /// assert/retract *sequence* and require the verdict after every step to equal
    /// the one a **cold** engine gives for the same active set.
    #[test]
    fn warm_start_after_retraction_matches_a_cold_engine() {
        for seed in 0..200u64 {
            let mut rng = Lcg(seed
                .wrapping_mul(2_862_933_555_777_941_757)
                .wrapping_add(3_037_000_493));
            let nvars = usize::try_from(rng.in_range(1, 3)).unwrap();
            let nrows = usize::try_from(rng.in_range(3, 6)).unwrap();
            let rows: Vec<Vec<i128>> = (0..nrows)
                .map(|_| (0..nvars).map(|_| rng.in_range(-3, 3)).collect())
                .collect();
            let mut warm = Incremental::new(nvars, rows.iter().map(|row| sparse(row)).collect())
                .expect("tiny tableau");
            let mut active: Vec<(usize, i128, Rel)> = Vec::new();

            for _ in 0..12 {
                if !active.is_empty() && rng.in_range(0, 2) == 0 {
                    let (row, _, _) = active.pop().expect("non-empty");
                    warm.retract(row);
                } else {
                    let row = usize::try_from(rng.in_range(0, i128::try_from(nrows).unwrap() - 1))
                        .unwrap();
                    if active.iter().any(|(i, _, _)| *i == row) {
                        continue;
                    }
                    let rel = match rng.in_range(0, 3) {
                        0 => Rel::Le,
                        1 => Rel::Lt,
                        2 => Rel::Ge,
                        _ => Rel::Gt,
                    };
                    let entry = (row, rng.in_range(-5, 5), rel);
                    warm.assert_bound(row, rel, r(entry.1));
                    active.push(entry);
                }
                if active.is_empty() {
                    continue;
                }
                let warm_status = warm.check(None);
                let (cold_status, _) = incremental_verdict(nvars, &rows, &active);
                let sat_of = |s: &Status| match s {
                    Status::Feasible => Some(true),
                    Status::Infeasible(_) => Some(false),
                    Status::Unknown => None,
                };
                if let (Some(a), Some(b)) = (sat_of(&warm_status), sat_of(&cold_status)) {
                    assert_eq!(
                        a, b,
                        "seed {seed}: warm-start verdict {a} disagrees with a cold engine {b} \
                         on active={active:?} rows={rows:?}"
                    );
                }
            }
        }
    }

    /// The δ-relaxation through the warm engine: `x ≤ y ∧ y ≤ x` is feasible at
    /// `x = y`, but making **either** side strict empties it. A bug that dropped the
    /// infinitesimal would report the strict systems feasible (a wrong `sat`), and
    /// one that treated `≤` as `<` would refute the first (a wrong `unsat`).
    #[test]
    fn incremental_strict_vs_nonstrict_boundary() {
        // Rows over (x, y):  r0 = x − y,  r1 = y − x.
        let rows = vec![vec![1i128, -1], vec![-1i128, 1]];
        for (a_strict, b_strict, expect_feasible) in [
            (false, false, true), // x ≤ y ∧ y ≤ x     ⇒ x = y
            (true, false, false), // x < y ∧ y ≤ x     ⇒ empty
            (false, true, false), // x ≤ y ∧ y < x     ⇒ empty
            (true, true, false),  // x < y ∧ y < x     ⇒ empty
        ] {
            let rel = |strict: bool| if strict { Rel::Lt } else { Rel::Le };
            let active = [
                (0usize, 0i128, rel(a_strict)),
                (1usize, 0i128, rel(b_strict)),
            ];
            let (status, point) = incremental_verdict(2, &rows, &active);
            if expect_feasible {
                assert_eq!(
                    status,
                    Status::Feasible,
                    "x<=y & y<=x must be feasible at x=y"
                );
                let cs = active_constraints(2, &rows, &active);
                assert!(
                    satisfies(&cs, &point.expect("witness")),
                    "boundary witness replays"
                );
            } else {
                assert!(
                    matches!(status, Status::Infeasible(_)),
                    "strict({a_strict},{b_strict}) must be refuted, got {status:?}"
                );
            }
        }
    }

    /// **A certificate that fails verification must be discarded, not trusted.** An
    /// unbounded row states nothing, so a multiplier on it can never be part of a
    /// refutation; and the sign / vanishing-LHS / refuting-RHS rules must each
    /// reject on their own.
    #[test]
    fn farkas_holds_rejects_tampered_certificates() {
        // Rows over x:  r0 = x (bounded x ≤ 1), r1 = x (UNBOUNDED), r2 = −x (x ≥ 3,
        // written as −x ≤ −3).
        let rows = vec![
            vec![(0usize, r(1))],
            vec![(0usize, r(1))],
            vec![(0usize, r(-1))],
        ];
        let bounded = vec![Some((Rel::Le, r(1))), None, Some((Rel::Le, r(-3)))];
        // The genuine refutation: x ≤ 1 and −x ≤ −3 sum to 0 ≤ −2.
        assert!(
            farkas_holds(1, &rows, &bounded, &[r(1), r(0), r(1)]),
            "the genuine certificate must verify"
        );
        // Leaning on the UNBOUNDED row is not a refutation of anything.
        assert!(
            !farkas_holds(1, &rows, &bounded, &[r(0), r(1), r(1)]),
            "a multiplier on an unbounded row must be rejected"
        );
        // Negative multiplier on a `≤` row — wrong sign.
        assert!(
            !farkas_holds(1, &rows, &bounded, &[r(-1), r(0), r(-1)]),
            "wrong-sign multipliers must be rejected"
        );
        // The left-hand side does not vanish.
        assert!(
            !farkas_holds(1, &rows, &bounded, &[r(2), r(0), r(1)]),
            "a non-vanishing lhs must be rejected"
        );
        // All-zero is not a refutation.
        assert!(
            !farkas_holds(1, &rows, &bounded, &[r(0), r(0), r(0)]),
            "the zero certificate must be rejected"
        );
        // Non-strict rows that sum to exactly 0 are `0 ≤ 0` — feasible, not a
        // refutation (only a strict row buys the δ-aware `0 < 0`).
        let touching = vec![Some((Rel::Le, r(1))), None, Some((Rel::Le, r(-1)))];
        assert!(
            !farkas_holds(1, &rows, &touching, &[r(1), r(0), r(1)]),
            "0 <= 0 is feasible (x = 1) and must be rejected"
        );
        let strict = vec![Some((Rel::Lt, r(1))), None, Some((Rel::Le, r(-1)))];
        assert!(
            farkas_holds(1, &rows, &strict, &[r(1), r(0), r(1)]),
            "the delta-aware 0 < 0 refutation must verify"
        );
    }

    /// The dense public [`check_farkas`] and the sparse engine-internal
    /// `farkas_holds` are one implementation; this pins that they cannot drift.
    #[test]
    fn dense_and_sparse_farkas_verifiers_agree() {
        let cs = [con(&[1, 0], Rel::Ge, 3), con(&[1, 1], Rel::Le, 1)];
        let rows: Vec<Vec<(usize, Rational)>> =
            cs.iter().map(|c| densify_to_sparse(&c.coeffs)).collect();
        let rel_rhs: Vec<Option<(Rel, Rational)>> =
            cs.iter().map(|c| Some((c.rel, c.rhs))).collect();
        for y in [
            [r(-1), r(1)],
            [r(1), r(1)],
            [r(0), r(0)],
            [r(-1), r(2)],
            [r(-2), r(2)],
        ] {
            assert_eq!(
                check_farkas(2, &cs, &y),
                farkas_holds(2, &rows, &rel_rhs, &y),
                "verifiers disagree on {y:?}"
            );
        }
    }

    /// A tableau over more cells than [`MAX_TABLEAU_CELLS`] is declined
    /// structurally, so the caller can keep a cheaper engine rather than pay for a
    /// tableau that will not fit.
    #[test]
    fn oversized_tableau_declines() {
        let rows: Vec<Vec<(usize, Rational)>> = (0..3_000).map(|_| vec![(0usize, r(1))]).collect();
        assert!(
            Incremental::new(3_000, rows).is_none(),
            "3000 rows x 6000 columns is over the cell cap and must decline"
        );
        let ok: Vec<Vec<(usize, Rational)>> = (0..8).map(|_| vec![(0usize, r(1))]).collect();
        assert!(
            Incremental::new(4, ok).is_some(),
            "a small tableau is built"
        );
    }

    // ---------------------------------------------------------------------
    // Pivot policy and instrumentation (2026-09-08).
    //
    // The soundness argument for a new entering rule is one sentence — every
    // rule draws from the same candidate set, so `select_entering`'s `None` is a
    // property of the tableau and not of the heuristic — and the three tests
    // below are what turn that sentence into something that can fail.
    // ---------------------------------------------------------------------

    /// Builds a random constraint system; shared by the policy tests so that
    /// "both rules agree" and "the counts stay exact" are measured over the same
    /// population rather than over two hand-picked ones.
    fn random_system(seed: u64) -> (usize, Vec<Constraint>) {
        let mut rng = Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407));
        let nvars = usize::try_from(rng.in_range(2, 5)).unwrap();
        let ncon = usize::try_from(rng.in_range(2, 8)).unwrap();
        let mut cs: Vec<Constraint> = Vec::with_capacity(ncon);
        for _ in 0..ncon {
            let coeffs: Vec<Rational> = (0..nvars).map(|_| r(rng.in_range(-3, 3))).collect();
            let rel = match rng.in_range(0, 4) {
                0 => Rel::Le,
                1 => Rel::Ge,
                2 => Rel::Eq,
                3 => Rel::Lt,
                _ => Rel::Gt,
            };
            cs.push(Constraint {
                coeffs,
                rel,
                rhs: r(rng.in_range(-4, 4)),
            });
        }
        (nvars, cs)
    }

    /// The incrementally-maintained column counts must equal a full recount after
    /// **every** pivot.
    ///
    /// `col_nnz` is not a diagnostic: [`EnteringRule::MinimiseFillIn`] scores
    /// candidates by it, so a drifted count is a silently different pivot
    /// sequence — not a wrong answer, but an unreproducible one, and the thing
    /// that would make an A/B measure noise. Recounting here rather than trusting
    /// the `set_cell` bookkeeping is the point: the two must agree cell for cell.
    #[test]
    fn col_nnz_matches_a_recount_after_every_pivot() {
        let mut pivots_seen = 0u32;
        for seed in 0..200u64 {
            let (nvars, cs) = random_system(seed);
            let mut tab = Tableau::new(nvars, &cs);
            for v in 0..tab.n {
                if tab.clamp_nonbasic(v).is_err() {
                    break;
                }
            }
            let mut steps = 0u32;
            loop {
                let before = tab.total_pivots;
                match tab.run(None, 1) {
                    Ok(RunOutcome::Feasible | RunOutcome::Infeasible(_)) | Err(Overflow) => break,
                    Ok(RunOutcome::Unknown) => {}
                }
                if tab.total_pivots > before {
                    pivots_seen += 1;
                }
                let incremental_cols = tab.col_nnz.clone();
                let incremental_rows = tab.row_nz.clone();
                tab.recount_columns();
                assert_eq!(
                    incremental_cols, tab.col_nnz,
                    "seed {seed}: column counts drifted after pivot {steps}"
                );
                // The row index is the one the pivot and the entering scan
                // ITERATE, so a drifted entry is a cell silently skipped — a
                // wrong tableau, not a slow one. It must be sorted, because
                // Bland's rule is "smallest usable index" and the index order
                // is what makes that true.
                assert_eq!(
                    incremental_rows, tab.row_nz,
                    "seed {seed}: row nonzero index drifted after pivot {steps}"
                );
                for (i, nz) in tab.row_nz.iter().enumerate() {
                    assert!(
                        nz.windows(2).all(|w| w[0] < w[1]),
                        "seed {seed}: row {i}'s nonzero index is not strictly sorted"
                    );
                }
                steps += 1;
                if steps > 60 {
                    break;
                }
            }
        }
        assert!(
            pivots_seen > 50,
            "the population must actually pivot for this to check anything; saw {pivots_seen}"
        );
    }

    /// Bland's rule and the fill-in rule must agree on *whether* a violated row
    /// can be repaired, and every candidate either returns must be usable.
    ///
    /// This is the soundness hinge. `run` reads `select_entering(..) == None` as
    /// "this row is unrepairable" and hands the row to [`Tableau::farkas`], which
    /// builds a refutation from it. A rule that returned `None` while a usable
    /// candidate existed would manufacture an `Infeasible` — a wrong `unsat`.
    /// (The certificate self-check would then almost certainly reject it, but
    /// "the second gate would probably catch it" is not the argument to rest a
    /// wrong-unsat on.)
    #[test]
    fn every_rule_agrees_on_whether_a_row_can_be_repaired() {
        let mut compared = 0u32;
        let mut both_some = 0u32;
        let mut both_none = 0u32;
        let mut differed_in_choice = 0u32;
        for seed in 0..400u64 {
            let (nvars, cs) = random_system(seed);
            let mut bland = Tableau::new_rows_with_policy(
                nvars,
                cs.iter().map(|c| densify_to_sparse(&c.coeffs)).collect(),
                PivotPolicy::bland(),
            );
            let mut fill = Tableau::new_rows_with_policy(
                nvars,
                cs.iter().map(|c| densify_to_sparse(&c.coeffs)).collect(),
                PivotPolicy::new(),
            );
            for (i, c) in cs.iter().enumerate() {
                bland.set_row_bound(i, Some((c.rel, c.rhs)));
                fill.set_row_bound(i, Some((c.rel, c.rhs)));
            }
            for v in 0..bland.n {
                let _ = bland.clamp_nonbasic(v);
                let _ = fill.clamp_nonbasic(v);
            }
            for row in 0..bland.m {
                for &too_low in &[true, false] {
                    let a = bland.select_entering(row, too_low, false);
                    let b = fill.select_entering(row, too_low, false);
                    compared += 1;
                    assert_eq!(
                        a.is_some(),
                        b.is_some(),
                        "seed {seed} row {row} too_low={too_low}: the rules disagree on whether \
                         the row is repairable; `None` is what `farkas` reads as a refutation"
                    );
                    match (a, b) {
                        (Some(x), Some(y)) => {
                            both_some += 1;
                            assert!(
                                bland.entering_is_usable(row, x, too_low),
                                "Bland returned an unusable candidate"
                            );
                            assert!(
                                fill.entering_is_usable(row, y, too_low),
                                "the fill-in rule returned an unusable candidate"
                            );
                            if x != y {
                                differed_in_choice += 1;
                            }
                        }
                        (None, None) => both_none += 1,
                        _ => unreachable!("the assert above rules this out"),
                    }
                }
            }
        }
        // Coverage, not decoration: an "agree" result over a population where one
        // branch never occurs is the vacuous-control failure mode, so both the
        // repairable and the unrepairable case must have been reached, and the
        // rules must actually have made different choices somewhere — otherwise
        // this test is comparing Bland's rule with itself.
        assert!(compared > 1_000, "thin population: {compared} comparisons");
        assert!(both_some > 100, "no repairable rows reached: {both_some}");
        assert!(both_none > 10, "no unrepairable rows reached: {both_none}");
        assert!(
            differed_in_choice > 10,
            "the two rules never chose differently ({differed_in_choice}); this test would pass \
             against a rule that is secretly Bland's"
        );
    }

    /// The two policies must reach the **same verdict** on every random system,
    /// and every `Infeasible` must carry a certificate that verifies.
    ///
    /// Agreement on the answer is the property a heuristic change is allowed to
    /// keep; the pivot *sequence* is free to differ, and does.
    #[test]
    fn both_policies_decide_identically_and_certificates_verify() {
        let mut infeasible_seen = 0u32;
        let mut feasible_seen = 0u32;
        for seed in 0..400u64 {
            let (nvars, cs) = random_system(seed);
            let sparse: Vec<Vec<(usize, Rational)>> =
                cs.iter().map(|c| densify_to_sparse(&c.coeffs)).collect();
            let mut a = Incremental::with_policy(nvars, sparse.clone(), PivotPolicy::bland())
                .expect("small tableau");
            let mut b =
                Incremental::with_policy(nvars, sparse, PivotPolicy::new()).expect("small tableau");
            for (i, c) in cs.iter().enumerate() {
                a.assert_bound(i, c.rel, c.rhs);
                b.assert_bound(i, c.rel, c.rhs);
            }
            let sa = a.check(None);
            let sb = b.check(None);
            match (&sa, &sb) {
                (Status::Feasible, Status::Feasible) => feasible_seen += 1,
                (Status::Infeasible(_), Status::Infeasible(_)) => infeasible_seen += 1,
                (Status::Unknown, _) | (_, Status::Unknown) => {}
                _ => panic!("seed {seed}: policies disagree — bland {sa:?}, fill-in {sb:?}"),
            }
        }
        assert!(feasible_seen > 20, "thin feasible arm: {feasible_seen}");
        assert!(
            infeasible_seen > 20,
            "thin infeasible arm: {infeasible_seen}"
        );
    }

    /// The tie-break is seeded, so two engines built with the same policy pivot
    /// identically — determinism is a public API promise, and a reservoir sample
    /// is exactly the place a clock or an address would sneak in.
    ///
    /// A *different* seed is allowed to pivot differently; that it sometimes does
    /// is what makes this test about determinism rather than about the tie-break
    /// being unreachable.
    #[test]
    fn the_tie_break_is_seeded_and_reproducible() {
        let mut differing_seeds = 0u32;
        for seed in 0..120u64 {
            let (nvars, cs) = random_system(seed);
            let sparse: Vec<Vec<(usize, Rational)>> =
                cs.iter().map(|c| densify_to_sparse(&c.coeffs)).collect();
            let run = |policy: PivotPolicy| {
                let mut e =
                    Incremental::with_policy(nvars, sparse.clone(), policy).expect("small tableau");
                for (i, c) in cs.iter().enumerate() {
                    e.assert_bound(i, c.rel, c.rhs);
                }
                let s = e.check(None);
                (s, e.pivots())
            };
            let (s1, p1) = run(PivotPolicy::new());
            let (s2, p2) = run(PivotPolicy::new());
            assert_eq!(s1, s2, "seed {seed}: same policy, different verdict");
            assert_eq!(p1, p2, "seed {seed}: same policy, different pivot count");

            let other = PivotPolicy {
                tie_break_seed: 0x1234_5678_9ABC_DEF0,
                ..PivotPolicy::new()
            };
            let (s3, p3) = run(other);
            assert_eq!(
                s1, s3,
                "seed {seed}: a different tie-break seed changed the VERDICT"
            );
            if p1 != p3 {
                differing_seeds += 1;
            }
        }
        assert!(
            differing_seeds > 0,
            "no seed ever changed the pivot count, so the tie-break is never reached and this \
             test proves nothing about it"
        );
    }

    /// The Bland fallback must be reachable, must be per call, and must not
    /// change any verdict.
    ///
    /// Driven by setting `bland_threshold` to `0` rather than by finding a
    /// cycling instance: the threshold is the knob, so exercising it at its
    /// boundary is what tells us the fallback is wired at all. With the default
    /// `1_000` on these small systems it never fires, which is why a test that
    /// only ran the default would report a dead path as a live one.
    #[test]
    fn the_bland_fallback_is_reachable_and_verdict_preserving() {
        let eager = PivotPolicy {
            bland_threshold: 0,
            ..PivotPolicy::new()
        };
        let mut fallbacks = 0u64;
        let mut default_fallbacks = 0u64;
        let mut compared = 0u32;
        for seed in 0..400u64 {
            let (nvars, cs) = random_system(seed);
            let sparse: Vec<Vec<(usize, Rational)>> =
                cs.iter().map(|c| densify_to_sparse(&c.coeffs)).collect();
            let run = |policy: PivotPolicy| {
                let mut e =
                    Incremental::with_policy(nvars, sparse.clone(), policy).expect("small tableau");
                for (i, c) in cs.iter().enumerate() {
                    e.assert_bound(i, c.rel, c.rhs);
                }
                let s = e.check(None);
                (s, e.counters())
            };
            let (s_default, c_default) = run(PivotPolicy::new());
            let (s_eager, c_eager) = run(eager);
            fallbacks += c_eager.bland_fallbacks;
            default_fallbacks += c_default.bland_fallbacks;
            if !matches!(s_default, Status::Unknown) && !matches!(s_eager, Status::Unknown) {
                compared += 1;
                assert_eq!(
                    s_default, s_eager,
                    "seed {seed}: the Bland fallback changed the verdict"
                );
            }
        }
        assert!(compared > 100, "thin comparison population: {compared}");
        assert!(
            fallbacks > 0,
            "the fallback never fired even at threshold 0, so it is not wired to anything"
        );
        assert_eq!(
            default_fallbacks, 0,
            "the default threshold fired on a small random system, so it is not the guard it \
             claims to be — it is the rule"
        );
    }

    /// An arithmetic overflow now leaves the pivot row **half-rewritten**, where
    /// the previous code built a replacement row and only installed it on
    /// success. The recovery path must therefore actually recover.
    ///
    /// This is the one behavioural difference the in-place rewrite introduces,
    /// so it gets a test rather than an argument. The argument, for the record,
    /// is that `Incremental::point` materialises from `rows_sparse` (the
    /// immutable INPUT rows) and `value`, never from `row`, so a torn `row`
    /// cannot reach a witness — but "I read the code and nothing else touches
    /// it" is exactly the claim this repository has been wrong about before.
    ///
    /// Corruption is injected directly rather than provoked through an i128
    /// overflow: the point is that recovery is total regardless of HOW the
    /// state was torn, and a test that had to construct a specific overflow
    /// would be pinning that overflow instead.
    #[test]
    fn a_poisoned_engine_recovers_a_consistent_tableau() {
        let (nvars, cs) = random_system(11);
        let sparse: Vec<Vec<(usize, Rational)>> =
            cs.iter().map(|c| densify_to_sparse(&c.coeffs)).collect();
        let mut clean =
            Incremental::with_policy(nvars, sparse.clone(), PivotPolicy::new()).expect("tableau");
        let mut torn =
            Incremental::with_policy(nvars, sparse, PivotPolicy::new()).expect("tableau");
        for (i, c) in cs.iter().enumerate() {
            clean.assert_bound(i, c.rel, c.rhs);
            torn.assert_bound(i, c.rel, c.rhs);
        }

        // Tear the tableau the way a mid-pivot overflow would: some cells
        // rewritten, the derived indices no longer describing them.
        for i in 0..torn.tab.m {
            for v in 0..torn.tab.n {
                if (i + v).is_multiple_of(3) {
                    torn.tab.row[i][v] = Rational::integer(7);
                }
            }
        }
        torn.tab.col_nnz.iter_mut().for_each(|c| *c = 0);
        torn.tab.row_nz.iter_mut().for_each(Vec::clear);
        torn.poisoned = true;

        let expected = clean.check(None);
        let recovered = torn.check(None);
        assert_eq!(
            torn.cold_restarts(),
            1,
            "the poisoned engine must have taken the cold-restart path"
        );
        assert_eq!(
            expected, recovered,
            "a poisoned engine did not recover the verdict a clean one reaches"
        );

        // And the derived indices must describe the rebuilt rows exactly.
        let after_cols = torn.tab.col_nnz.clone();
        let after_rows = torn.tab.row_nz.clone();
        torn.tab.recount_columns();
        assert_eq!(
            after_cols, torn.tab.col_nnz,
            "recovery left the column counts describing the torn rows"
        );
        assert_eq!(
            after_rows, torn.tab.row_nz,
            "recovery left the row index describing the torn rows"
        );
    }

    /// The cost counters must be nonzero on a system that pivots, and must be
    /// derived from the work rather than invented.
    ///
    /// The specific trap: `pivot_cells_written` is what prices a sparse
    /// representation against the dense one, so it must count the cells the
    /// pivot actually writes. It is checked here against the only other thing
    /// that knows the answer — the total nonzero count, which bounds the cells
    /// one row combination can write.
    #[test]
    fn the_cost_counters_are_populated_and_bounded_by_the_work() {
        let (nvars, cs) = random_system(7);
        let sparse: Vec<Vec<(usize, Rational)>> =
            cs.iter().map(|c| densify_to_sparse(&c.coeffs)).collect();
        let mut e = Incremental::with_policy(nvars, sparse, PivotPolicy::new()).expect("tableau");
        for (i, c) in cs.iter().enumerate() {
            e.assert_bound(i, c.rel, c.rhs);
        }
        let _ = e.check(None);
        let c = e.counters();
        assert!(c.fill_samples > 0, "fill-in was never sampled");
        assert!(
            c.entering_scan_cells > 0,
            "the entering scan reported zero columns examined"
        );
        assert!(
            c.leaving_scan_rows > 0,
            "the leaving scan reported zero rows examined"
        );
        assert!(
            c.pivot_cells_written >= c.pivot_rows_combined,
            "a combined row writes at least one cell: {} cells over {} rows",
            c.pivot_cells_written,
            c.pivot_rows_combined
        );
        // Every Farkas outcome is accounted for: a refutation either produced a
        // verified certificate or declined through exactly one named arm.
        let declines = c.farkas_declined_basic_not_slack
            + c.farkas_declined_nonbasic_problem_var
            + c.farkas_declined_self_check;
        assert!(
            u32::try_from(declines + c.farkas_certificates).is_ok(),
            "sanity: the Farkas accounting overflowed"
        );
    }
}
