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
//! materializes a concrete rational witness by choosing `δ` small enough. Still to
//! come (P1.9 · T1.9.2+): routing into [`crate::lra`] behind a size threshold, and
//! Farkas-certificate *extraction* from the tableau (T1.9.3; the verifier
//! [`check_farkas`] is already here).
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

use axeyum_ir::Rational;

/// The comparator of a constraint row `Σ aⱼ·xⱼ ⋈ b`.
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
    match Tableau::new(nvars, constraints).solve() {
        Ok(outcome) => outcome,
        Err(Overflow) => SimplexOutcome::Unknown,
    }
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
    /// The original input constraints, retained for concrete-witness materialization.
    constraints: Vec<Constraint>,
}

impl Tableau {
    fn new(nvars: usize, constraints: &[Constraint]) -> Tableau {
        let m = constraints.len();
        let n = nvars + m;
        let mut lower = vec![None; n];
        let mut upper = vec![None; n];
        let mut row = vec![vec![Rational::zero(); n]; m];
        let mut basic = vec![0usize; m];
        let mut is_basic = vec![false; n];

        for (i, c) in constraints.iter().enumerate() {
            let slack = nvars + i;
            basic[i] = slack;
            is_basic[slack] = true;
            // slackᵢ = Σ aᵢⱼ·xⱼ  ⇒ row over the (nonbasic) problem vars.
            for (j, &a) in c.coeffs.iter().enumerate() {
                row[i][j] = a;
            }
            // Bounds from the comparator: slackᵢ ⋈ bᵢ, in ℚ(δ). Strict `<`/`>`
            // shrink the bound by one infinitesimal: `x < b` ⇔ `x ≤ b − δ`.
            let b = Delta::num(c.rhs);
            let b_minus_d = Delta {
                c: c.rhs,
                k: Rational::integer(-1),
            };
            let b_plus_d = Delta {
                c: c.rhs,
                k: Rational::integer(1),
            };
            match c.rel {
                Rel::Le => upper[slack] = Some(b),
                Rel::Ge => lower[slack] = Some(b),
                Rel::Eq => {
                    lower[slack] = Some(b);
                    upper[slack] = Some(b);
                }
                Rel::Lt => upper[slack] = Some(b_minus_d),
                Rel::Gt => lower[slack] = Some(b_plus_d),
            }
        }

        // Initial assignment: nonbasic problem vars = 0; each slack = Σ aᵢⱼ·0 = 0.
        let value = vec![Delta::zero(); n];
        Tableau {
            n,
            nvars,
            m,
            basic,
            row,
            value,
            lower,
            upper,
            is_basic,
            constraints: constraints.to_vec(),
        }
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
    /// entering nonbasic variable).
    fn solve(mut self) -> R<SimplexOutcome> {
        loop {
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
                // All bounds satisfied → feasible. Materialize a concrete rational
                // point from the δ-assignment (choose δ small enough).
                return Ok(SimplexOutcome::Feasible(self.materialize()?));
            };

            let b = self.basic[r];
            // Choose the entering nonbasic variable by Bland's rule.
            let entering = self.select_entering(r, too_low)?;
            let Some(j) = entering else {
                // No way to repair row `r` → infeasible. Build the Farkas cert.
                return Ok(SimplexOutcome::Infeasible(self.farkas(r, too_low)?));
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
        for i in 0..self.m {
            if i == r {
                continue;
            }
            let coeff = self.row[i][enter];
            if coeff.is_zero() {
                continue;
            }
            // row_i := row_i + coeff · new_row (eliminating `enter`'s column).
            let base = self.row[r].clone();
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
        for c in &self.constraints {
            // Row δ-value (C, K) over the problem variables.
            let mut cc = Rational::zero();
            let mut kk = Rational::zero();
            for (j, &a) in c.coeffs.iter().enumerate() {
                if a.is_zero() {
                    continue;
                }
                cc = add(cc, mul(a, self.value[j].c)?)?;
                kk = add(kk, mul(a, self.value[j].k)?)?;
            }
            // `margin = |b − C|`; the row binds ε only when C is strictly inside the
            // bound (margin > 0) and K pushes toward it. Then ε < margin / |K|.
            let margin = sub(c.rhs, cc)?; // b − C
            if margin.is_zero() || kk.is_zero() {
                continue;
            }
            // Toward-violation test: for an upper bound (Le/Lt) K>0 pushes up toward
            // b; for a lower bound (Ge/Gt) K<0 pushes down toward b. When margin and
            // the push have the shape that could cross, cap ε.
            let k_pos = cmp(kk, Rational::zero())? == core::cmp::Ordering::Greater;
            let toward = match c.rel {
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

    /// Farkas-certificate extraction from the infeasible row `r`.
    ///
    /// **Deferred to P1.9 · T1.9.3.** Extracting the exact nonnegative combination
    /// over the input rows from the final tableau (with the correct `≤`/`≥`/`=`
    /// sign discipline and the δ-relaxation once strict rows land) is its own
    /// slice. Until then this returns an **empty** vector — a self-checkable
    /// "no certificate yet" that a caller must handle by falling back to the
    /// reference Fourier–Motzkin certificate. The infeasibility *decision* itself is
    /// exact and complete; only the machine-checkable witness is pending.
    #[allow(clippy::unused_self, clippy::unnecessary_wraps)]
    fn farkas(&self, _r: usize, _too_low: bool) -> R<Vec<Rational>> {
        Ok(Vec::new())
    }
}

/// Re-check a Farkas certificate `y` against the input `constraints`: every `y`
/// respects its row's sign (`≥0` for `≤`, `≤0` for `≥`, free for `=`), the combined
/// left-hand side vanishes (`Σ yᵢ·aᵢⱼ = 0` for every column `j`), and the combined
/// right-hand side is negative (`Σ yᵢ·bᵢ < 0`). Used by the tests here and by any
/// caller before trusting an `Infeasible` verdict.
#[must_use]
pub fn check_farkas(nvars: usize, constraints: &[Constraint], y: &[Rational]) -> bool {
    if y.len() != constraints.len() || y.iter().all(|v| v.is_zero()) {
        return false;
    }
    // Sign discipline per row.
    for (yi, c) in y.iter().zip(constraints) {
        let Some(s) = yi.checked_cmp(&Rational::zero()) else {
            return false;
        };
        match c.rel {
            // `≤`/`<` rows take a ≥0 multiplier; `≥`/`>` rows a ≤0 one; `=` is free.
            Rel::Le | Rel::Lt if s == core::cmp::Ordering::Less => return false,
            Rel::Ge | Rel::Gt if s == core::cmp::Ordering::Greater => return false,
            _ => {}
        }
    }
    // Column sums must vanish.
    for j in 0..nvars {
        let mut acc = Rational::zero();
        for (yi, c) in y.iter().zip(constraints) {
            let Some(t) = yi.checked_mul(c.coeffs[j]) else {
                return false;
            };
            let Some(s) = acc.checked_add(t) else {
                return false;
            };
            acc = s;
        }
        if !acc.is_zero() {
            return false;
        }
    }
    // Combined rhs must be strictly negative.
    let mut rhs = Rational::zero();
    for (yi, c) in y.iter().zip(constraints) {
        let Some(t) = yi.checked_mul(c.rhs) else {
            return false;
        };
        let Some(s) = rhs.checked_add(t) else {
            return false;
        };
        rhs = s;
    }
    matches!(
        rhs.checked_cmp(&Rational::zero()),
        Some(core::cmp::Ordering::Less)
    )
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
    fn single_var_infeasible() {
        // x ≥ 3 ∧ x ≤ 1 → infeasible (the decision; the machine-checkable Farkas
        // witness is T1.9.3, so the cert vector is empty for now).
        let cs = [con(&[1], Rel::Ge, 3), con(&[1], Rel::Le, 1)];
        match feasible(1, &cs) {
            SimplexOutcome::Infeasible(y) => {
                assert!(y.is_empty() || check_farkas(1, &cs, &y));
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
                // If a closed-form cert was produced, it must re-check; an empty
                // cert (conservative bail) is allowed by this slice.
                assert!(y.is_empty() || check_farkas(2, &cs, &y));
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
        // x + y = 3 ∧ x + y = 5 → infeasible.
        let cs = [con(&[1, 1], Rel::Eq, 3), con(&[1, 1], Rel::Eq, 5)];
        assert!(matches!(feasible(2, &cs), SimplexOutcome::Infeasible(_)));
    }

    #[test]
    fn empty_constraints_feasible() {
        assert!(matches!(feasible(2, &[]), SimplexOutcome::Feasible(_)));
    }

    #[test]
    fn strict_contradiction_infeasible() {
        // x < 1 ∧ x > 1 → infeasible (the δ-relaxation makes the strict bounds
        // exact: x ≤ 1−δ ∧ x ≥ 1+δ is empty).
        let cs = [con(&[1], Rel::Lt, 1), con(&[1], Rel::Gt, 1)];
        assert!(matches!(feasible(1, &cs), SimplexOutcome::Infeasible(_)));
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
                SimplexOutcome::Infeasible(_) => Some(false),
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
}
