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
//!   Fourier–Motzkin path's [`crate::lra`] already consumes, or
//! - [`SimplexOutcome::Unknown`] iff the exact `i128` rational arithmetic overflows
//!   (never a wrong verdict — the same `checked_*` discipline as the rest of the
//!   solver).
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
//!   offline [`crate::lra`] overflow fallback).
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
/// columns). A `Rational` is two `i128`s, so 4M cells is ~128 MB — past that the
/// dense general simplex is the wrong data structure and the caller keeps whatever
/// engine it had. Purely structural (no clock), so the decline is deterministic.
pub(crate) const MAX_TABLEAU_CELLS: usize = 4_000_000;

/// Pivot ceiling for a single [`feasible`] / [`Incremental::check`] call. Bland's
/// rule already guarantees termination; this is the deterministic belt so a run
/// with **no** wall-clock deadline still cannot spin unboundedly on a pathological
/// instance. Exhaustion yields [`SimplexOutcome::Unknown`] — sound, never a verdict.
const MAX_PIVOTS: u64 = 2_000_000;

/// Whether a caller-owned absolute deadline has passed.
fn past_deadline(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// The comparator of a constraint row `Σ aⱼ·xⱼ ⋈ b`.
///
/// The full set is part of the feasibility API (and exercised by the tests); both
/// in-tree callers — the LRA fallback in [`crate::lra`] and the online
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
    /// Exact arithmetic overflowed — a sound `unknown`, never a verdict.
    Unknown,
}

/// Marker for an `i128`-rational overflow; mapped to [`SimplexOutcome::Unknown`].
struct Overflow;
type R<T> = Result<T, Overflow>;

fn add(a: Rational, b: Rational) -> R<Rational> {
    a.checked_add(b).ok_or(Overflow)
}
fn sub(a: Rational, b: Rational) -> R<Rational> {
    a.checked_sub(b).ok_or(Overflow)
}
fn mul(a: Rational, b: Rational) -> R<Rational> {
    a.checked_mul(b).ok_or(Overflow)
}
fn div(a: Rational, b: Rational) -> R<Rational> {
    a.checked_div(b).ok_or(Overflow)
}
fn cmp(a: Rational, b: Rational) -> R<core::cmp::Ordering> {
    a.checked_cmp(&b).ok_or(Overflow)
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
    /// `δ > 0`.
    fn cmp(self, o: Delta) -> R<core::cmp::Ordering> {
        Ok(match cmp(self.c, o.c)? {
            core::cmp::Ordering::Equal => cmp(self.k, o.k)?,
            ord => ord,
        })
    }
}

/// Decide feasibility of the conjunction of `constraints` over `nvars` variables.
///
/// See the module docs for the outcome contract. `nvars` must equal every
/// `constraint.coeffs.len()`.
///
/// # Panics
///
/// Panics if a constraint's `coeffs` length differs from `nvars` (a caller bug).
#[must_use]
pub fn feasible(nvars: usize, constraints: &[Constraint]) -> SimplexOutcome {
    for c in constraints {
        assert_eq!(c.coeffs.len(), nvars, "constraint arity mismatch");
    }
    let mut tableau = Tableau::new(nvars, constraints);
    match tableau.run(None, MAX_PIVOTS) {
        Ok(RunOutcome::Feasible) => match tableau.materialize() {
            Ok(point) => SimplexOutcome::Feasible(point),
            Err(Overflow) => SimplexOutcome::Unknown,
        },
        Ok(RunOutcome::Infeasible(y)) => SimplexOutcome::Infeasible(y),
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
    /// Farkas certificate; [`farkas_holds`] rejects any candidate that puts a
    /// nonzero multiplier on one.
    rel_rhs: Vec<Option<(Rel, Rational)>>,
}

impl Tableau {
    /// A tableau over `rows_sparse` with **no** bounds imposed (every row inactive).
    fn new_rows(nvars: usize, rows_sparse: Vec<Vec<(usize, Rational)>>) -> Tableau {
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
            && self.value[v].cmp(hi)? == core::cmp::Ordering::Greater
        {
            return self.update_nonbasic(v, hi);
        }
        if let Some(lo) = self.lower[v]
            && self.value[v].cmp(lo)? == core::cmp::Ordering::Less
        {
            return self.update_nonbasic(v, lo);
        }
        Ok(())
    }

    /// Whether `v`'s value is below its lower bound.
    fn below_lower(&self, v: usize) -> R<bool> {
        Ok(match self.lower[v] {
            Some(lo) => self.value[v].cmp(lo)? == core::cmp::Ordering::Less,
            None => false,
        })
    }
    /// Whether `v`'s value is above its upper bound.
    fn above_upper(&self, v: usize) -> R<bool> {
        Ok(match self.upper[v] {
            Some(hi) => self.value[v].cmp(hi)? == core::cmp::Ordering::Greater,
            None => false,
        })
    }

    /// Can nonbasic `v` increase (strictly below its upper bound, or unbounded)?
    fn can_increase(&self, v: usize) -> R<bool> {
        Ok(match self.upper[v] {
            Some(hi) => self.value[v].cmp(hi)? == core::cmp::Ordering::Less,
            None => true,
        })
    }
    /// Can nonbasic `v` decrease (strictly above its lower bound, or unbounded)?
    fn can_decrease(&self, v: usize) -> R<bool> {
        Ok(match self.lower[v] {
            Some(lo) => self.value[v].cmp(lo)? == core::cmp::Ordering::Greater,
            None => true,
        })
    }

    /// The main feasibility loop (Bland's rule on the basic variable, then on the
    /// entering nonbasic variable). Resumes from whatever basis/assignment the
    /// tableau currently holds — which is what makes [`Incremental`] warm.
    ///
    /// `budget` bounds the pivot count and `deadline` the wall clock; exhausting
    /// either yields [`SimplexOutcome::Unknown`] (sound, never a verdict).
    fn run(&mut self, deadline: Option<Instant>, budget: u64) -> R<RunOutcome> {
        let mut pivots: u64 = 0;
        loop {
            // Polled on entry too, so an already-expired deadline does no work at
            // all and reports `Unknown` rather than a verdict the caller did not
            // budget for.
            if pivots.is_multiple_of(64) && past_deadline(deadline) {
                return Ok(RunOutcome::Unknown);
            }
            if pivots >= budget {
                return Ok(RunOutcome::Unknown);
            }
            pivots += 1;
            // Smallest-index basic variable that violates a bound.
            let mut viol: Option<(usize, bool)> = None; // (row, too_low)
            for i in 0..self.m {
                let b = self.basic[i];
                if self.below_lower(b)? {
                    viol = Some((i, true));
                    break;
                }
                if self.above_upper(b)? {
                    viol = Some((i, false));
                    break;
                }
            }
            let Some((r, too_low)) = viol else {
                // All bounds satisfied → feasible.
                return Ok(RunOutcome::Feasible);
            };

            let b = self.basic[r];
            // Choose the entering nonbasic variable by Bland's rule.
            let entering = self.select_entering(r, too_low)?;
            let Some(j) = entering else {
                // No way to repair row `r` → infeasible. Build the Farkas cert.
                return Ok(RunOutcome::Infeasible(self.farkas(r, too_low)?));
            };

            // Target value for the leaving basic variable: its violated bound.
            let target = if too_low {
                self.lower[b].expect("violated lower ⇒ bound exists")
            } else {
                self.upper[b].expect("violated upper ⇒ bound exists")
            };
            self.pivot_and_update(r, j, target)?;
        }
    }

    /// Bland's-rule entering-variable selection for repairing row `r` whose basic
    /// variable is too low (`too_low`) or too high. Returns the smallest-index
    /// nonbasic variable that can move the basic variable toward its bound.
    fn select_entering(&self, r: usize, too_low: bool) -> R<Option<usize>> {
        for v in 0..self.n {
            if self.is_basic[v] {
                continue;
            }
            let a = self.row[r][v];
            if a.is_zero() {
                continue;
            }
            let a_pos = cmp(a, Rational::zero())? == core::cmp::Ordering::Greater;
            // To INCREASE the basic var (too_low): raise a nonbasic with a>0 that can
            // increase, or lower one with a<0 that can decrease. To DECREASE: mirror.
            let usable = if too_low {
                (a_pos && self.can_increase(v)?) || (!a_pos && self.can_decrease(v)?)
            } else {
                (a_pos && self.can_decrease(v)?) || (!a_pos && self.can_increase(v)?)
            };
            if usable {
                return Ok(Some(v));
            }
        }
        Ok(None)
    }

    /// Pivot nonbasic `enter` into the basis in row `r` (whose current basic var
    /// `leave` moves to nonbasic at value `target`), then repair all rows.
    // The pivot rewrites parallel dense rows by column index `v`, indexing several
    // arrays at once — a plain range loop is the clearest form here.
    #[allow(clippy::needless_range_loop)]
    fn pivot_and_update(&mut self, r: usize, enter: usize, target: Delta) -> R<()> {
        let leave = self.basic[r];
        let a_re = self.row[r][enter];
        // Solve row r for `enter`:  leave = Σ a_rv·v  ⇒
        //   enter = (leave - Σ_{v≠enter} a_rv·v) / a_re, i.e. rewrite the row.
        // New row (for the now-basic `enter`): coefficient of `leave` becomes 1/a_re,
        // every other nonbasic v becomes -a_rv/a_re, and `enter`'s own column 0.
        let mut new_row = vec![Rational::zero(); self.n];
        for v in 0..self.n {
            if v == enter {
                continue;
            }
            if v == leave {
                continue;
            }
            new_row[v] = sub(Rational::zero(), div(self.row[r][v], a_re)?)?;
        }
        new_row[leave] = div(Rational::integer(1), a_re)?;
        // `enter` becomes basic in row r; `leave` becomes nonbasic.
        self.row[r] = new_row;
        self.basic[r] = enter;
        self.is_basic[enter] = true;
        self.is_basic[leave] = false;

        // Determine how far `enter` must move so that `leave` reaches `target`.
        //   leave_old = value[leave]; enter changes by θ; leave changes by a_re·θ.
        //   want leave_new = target ⇒ θ = (target - value[leave]) / a_re.
        let recip = div(Rational::integer(1), a_re)?;
        let theta = target.sub(self.value[leave])?.scale(recip)?;
        let enter_new = self.value[enter].add(theta)?;

        // Substitute `enter`'s new expression into every OTHER row and update values.
        // The pivot row is cloned ONCE, not per affected row — at a few thousand
        // columns the per-row clone was the dominant cost of a pivot.
        let base = self.row[r].clone();
        for i in 0..self.m {
            if i == r {
                continue;
            }
            let coeff = self.row[i][enter];
            if coeff.is_zero() {
                continue;
            }
            // row_i := row_i + coeff · new_row (eliminating `enter`'s column).
            for v in 0..self.n {
                let delta = mul(coeff, base[v])?;
                self.row[i][v] = add(self.row[i][v], delta)?;
            }
            self.row[i][enter] = Rational::zero();
        }

        // Update the stored values: leave → target, enter → enter_new, and every
        // basic variable recomputed from its (updated) row over the nonbasic vars.
        self.value[leave] = target;
        self.value[enter] = enter_new;
        for i in 0..self.m {
            let bi = self.basic[i];
            let mut acc = Delta::zero();
            for v in 0..self.n {
                if self.is_basic[v] {
                    continue;
                }
                if self.row[i][v].is_zero() {
                    continue;
                }
                acc = acc.add(self.value[v].scale(self.row[i][v])?)?;
            }
            self.value[bi] = acc;
        }
        Ok(())
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
            let k_pos = cmp(kk, Rational::zero())? == core::cmp::Ordering::Greater;
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
            let mag = if cmp(ratio, Rational::zero())? == core::cmp::Ordering::Less {
                sub(Rational::zero(), ratio)?
            } else {
                ratio
            };
            let half = mul(mag, Rational::checked_new(1, 2).ok_or(Overflow)?)?;
            if cmp(half, eps)? == core::cmp::Ordering::Less {
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
    fn farkas(&self, r: usize, too_low: bool) -> R<Vec<Rational>> {
        let b = self.basic[r];
        if b < self.nvars {
            // The infeasible basic variable must be a slack (problem vars are
            // unbounded and cannot violate a bound) — otherwise no closed form here.
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
                return Ok(Vec::new());
            }
            // yⱼ = −sign·aⱼ over the input row of slack `v`.
            y[v - self.nvars] = mul(sub(Rational::zero(), sign)?, a)?;
        }
        // Self-check: return the certificate only if it genuinely refutes the input.
        if farkas_holds(self.nvars, &self.rows_sparse, &self.rel_rhs, &y) {
            Ok(y)
        } else {
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
    /// The currently-bounded rows are jointly feasible; [`Incremental::point`]
    /// materializes the witness.
    Feasible,
    /// Infeasible. The payload is the set of **bounded row indices carrying a
    /// nonzero, self-verified Farkas multiplier** — the refutation's support. It is
    /// **empty** when no closed-form certificate could be extracted *and verified*:
    /// the infeasibility verdict itself is still sound (a basic variable is pinned
    /// outside its bound with no eligible entering variable), but the caller gets no
    /// minimized support and must fall back to a coarse explanation.
    Infeasible(Vec<usize>),
    /// Exact `i128` arithmetic overflowed, or the pivot/deadline budget ran out —
    /// a sound "don't know", never a verdict.
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
/// [`crate::lra_online`] normalizes every atom polarity into. Consequently no
/// variable ever has a lower bound, so the "lower > upper" immediate conflict of
/// the general algorithm cannot arise and every infeasibility is found by the
/// pivot loop, which is where the Farkas certificate comes from.
///
/// Every `Infeasible` support is self-verified by [`farkas_holds`] before it is
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
}

impl Incremental {
    /// Builds the warm engine over `nvars` problem variables and one row per
    /// `rows_sparse` entry, all rows initially **unbounded**.
    ///
    /// Returns `None` when the dense tableau would exceed [`MAX_TABLEAU_CELLS`] —
    /// a deterministic, purely structural decline that leaves the caller on
    /// whatever engine it had.
    pub fn new(nvars: usize, rows_sparse: Vec<Vec<(usize, Rational)>>) -> Option<Self> {
        let m = rows_sparse.len();
        let n = nvars.checked_add(m)?;
        if m.checked_mul(n)? > MAX_TABLEAU_CELLS {
            return None;
        }
        Some(Incremental {
            tab: Tableau::new_rows(nvars, rows_sparse),
            poisoned: false,
        })
    }

    /// Number of rows the engine was built over.
    pub fn rows(&self) -> usize {
        self.tab.m
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
        if self.poisoned {
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

    /// A concrete rational point for the problem variables after a
    /// [`Status::Feasible`] check, or `None` on overflow. The caller replays it
    /// against the original assertions — that replay, not this function, is what
    /// makes a `sat` trustworthy.
    pub(crate) fn point(&self) -> Option<Vec<Rational>> {
        self.tab.materialize().ok()
    }
}

/// Re-check a Farkas certificate `y` against the input `constraints`: every `y`
/// respects its row's sign (`≥0` for `≤`/`<`, `≤0` for `≥`/`>`, free for `=`), the
/// combined left-hand side vanishes (`Σ yᵢ·aᵢⱼ = 0` for every column `j`), and the
/// combined right-hand side refutes — `Σ yᵢ·bᵢ < 0`, or `= 0` when a strict (`<`/`>`)
/// row is used (the δ-aware `0 < 0`). Used by the tests here and by any caller
/// before trusting an `Infeasible` verdict.
// The dense public verifier is the module's *contract* surface: the in-tree callers
// verify differently ([`crate::lra`] rebuilds its own `FarkasCertificate`, the warm
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
    /// [`farkas_holds`] are one implementation; this pins that they cannot drift.
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
}
