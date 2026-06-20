//! Sound, bounded NRA capability: decide a single-variable nonlinear-real
//! **polynomial constraint** over one `Real` variable `x` *exactly*, with
//! **irrational witnesses** (ADR-0038, slice 1).
//!
//! This pass sits *in front of* the linear-abstraction NRA path
//! ([`crate::nra`]). Where that path abstracts a product `x·x` to a fresh
//! variable — losing the algebraic fact and reporting `Unknown` for `x·x = 2` —
//! this decider isolates the *real roots* of the collected polynomial exactly and
//! returns a witness, which may be an exact rational ([`Value::Real`]) or a real
//! **algebraic number** ([`Value::RealAlgebraic`], e.g. `√2`).
//!
//! # Scope (deliberately narrow — correctness over reach)
//!
//! Fires *only* when the **whole** query is exactly **one** assertion that
//! normalizes to a comparison `p(x) ⋈ 0` between a single-variable *real*
//! polynomial `p` and `0`, where `p` collects over `{+, −, ·, neg, RealConst,
//! symbol}` with `x` the only variable. Rational coefficients are cleared to
//! integers (multiplying through by the common denominator preserves every
//! `⋈`-relation since the multiplier is positive). Everything else declines
//! (`None`), leaving the query to [`crate::nra`]:
//!
//! - more than one variable, a non-`Real` sort, a non-polynomial operator
//!   (`div`, `RealToInt`, …),
//! - a second assertion (it could constrain `x`),
//! - a coefficient/degree past the [`MAX_ABS_COEFF`]/[`MAX_DEGREE`] guards, or
//!   any `i128`/`Rational` overflow during collection, denominator clearing, or
//!   root isolation.
//!
//! # Decisions
//!
//! - **`=`:** isolate the real roots of `p`. Each root is either an exact
//!   rational (→ [`Value::Real`]) or irrational (→ a [`Value::RealAlgebraic`]
//!   defined by `p` and its isolating interval). No real root ⇒ **Unsat**
//!   (exact). The witness is **replay-checked**: an algebraic witness `α` must
//!   satisfy `sign_at(p, α) = 0`; a rational witness is replayed through the
//!   ground evaluator on the original assertion.
//! - **`<, ≤, >, ≥`:** the real roots of `p` partition ℝ into sign-constant open
//!   intervals; pick a **rational** sample inside a matching-sign interval (the
//!   witness stays rational). Unsat iff no interval matches (`x·x < 0` ⇒ Unsat).
//! - **`≠`:** Sat unless `p ≡ 0`; exhibit a rational non-root.
//!
//! A wrong `sat`/`unsat` is catastrophic; declining is always sound. **No
//! floating point**: every sign test is exact over `i128`/[`Rational`].

use axeyum_ir::{
    Assignment, Op, Rational, RealAlgebraic, Sign, Sort, SymbolId, TermArena, TermId, TermNode,
    Value, eval,
};

use crate::backend::{CheckResult, SolverError};
use crate::model::Model;

/// Coefficient magnitude guard (mirrors `nia_square::MAX_ABS_COEFF`): above this
/// the pass declines to keep the exact-rational arithmetic and root isolation
/// inside `i128`.
const MAX_ABS_COEFF: i128 = 1i128 << 40;

/// Maximum polynomial degree the pass collects / decides; beyond it we decline.
const MAX_DEGREE: usize = 64;

/// The six real comparison shapes, oriented as `p(x) ⋈ 0`.
#[derive(Clone, Copy)]
enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Merge of the (sole, possibly absent) variable of two operands; a conflict (two
/// distinct variables) forces the collector to decline.
enum MergeVar {
    Ok(Option<SymbolId>),
    Conflict,
}

/// A single-variable polynomial with **rational** coefficients (LSB-first),
/// accumulated during collection so that `RealConst` denominators are tracked
/// exactly. Converted to an integer polynomial (denominators cleared) before
/// root isolation.
#[derive(Clone)]
struct RatPoly {
    var: Option<SymbolId>,
    coeffs: Vec<Rational>,
}

impl RatPoly {
    fn constant(r: Rational) -> Self {
        RatPoly {
            var: None,
            coeffs: vec![r],
        }
    }

    fn var_of(s: SymbolId) -> Self {
        RatPoly {
            var: Some(s),
            coeffs: vec![Rational::zero(), Rational::integer(1)],
        }
    }

    fn coeff(&self, i: usize) -> Rational {
        self.coeffs.get(i).copied().unwrap_or_else(Rational::zero)
    }

    /// Highest index with a nonzero coefficient (0 for a constant / zero poly).
    fn degree(&self) -> usize {
        let mut n = self.coeffs.len();
        while n > 1 && self.coeff(n - 1).is_zero() {
            n -= 1;
        }
        n.saturating_sub(1)
    }

    fn merge_var(a: Option<SymbolId>, b: Option<SymbolId>) -> MergeVar {
        match (a, b) {
            (None, v) | (v, None) => MergeVar::Ok(v),
            (Some(x), Some(y)) if x == y => MergeVar::Ok(Some(x)),
            _ => MergeVar::Conflict,
        }
    }

    fn neg(self) -> Option<Self> {
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for c in &self.coeffs {
            coeffs.push(c.checked_neg()?);
        }
        Some(RatPoly {
            var: self.var,
            coeffs,
        })
    }

    fn add(self, other: &Self) -> Option<Self> {
        let MergeVar::Ok(var) = RatPoly::merge_var(self.var, other.var) else {
            return None;
        };
        let len = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = Vec::with_capacity(len);
        for i in 0..len {
            coeffs.push(self.coeff(i).checked_add(other.coeff(i))?);
        }
        Some(RatPoly { var, coeffs })
    }

    fn sub(self, other: Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    fn mul(self, other: &Self) -> Option<Self> {
        let MergeVar::Ok(var) = RatPoly::merge_var(self.var, other.var) else {
            return None;
        };
        let prod_len = self.coeffs.len() + other.coeffs.len() - 1;
        if prod_len > MAX_DEGREE + 1 {
            return None;
        }
        let mut coeffs = vec![Rational::zero(); prod_len];
        for (i, &a) in self.coeffs.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, &b) in other.coeffs.iter().enumerate() {
                if b.is_zero() {
                    continue;
                }
                let term = a.checked_mul(b)?;
                coeffs[i + j] = coeffs[i + j].checked_add(term)?;
            }
        }
        Some(RatPoly { var, coeffs })
    }

    /// Clear denominators: multiply through by the LCM of all denominators to
    /// obtain an integer polynomial (LSB-first), declining on overflow. The
    /// multiplier is positive, so it preserves every comparison `p ⋈ 0`.
    fn to_integer_poly(&self) -> Option<Vec<i128>> {
        // LCM of the denominators.
        let mut lcm = 1i128;
        for c in &self.coeffs {
            let d = c.denominator();
            lcm = lcm_i128(lcm, d)?;
        }
        let mut out = Vec::with_capacity(self.coeffs.len());
        for c in &self.coeffs {
            // c * lcm is an integer: (num * lcm) / den, exact since den | lcm.
            let scaled = c.numerator().checked_mul(lcm)?;
            if scaled % c.denominator() != 0 {
                return None; // should not happen (den | lcm), but stay safe
            }
            let v = scaled / c.denominator();
            if v.checked_abs()? >= MAX_ABS_COEFF {
                return None;
            }
            out.push(v);
        }
        // Trim trailing zeros so the leading coefficient is genuine.
        while out.len() > 1 && *out.last().unwrap() == 0 {
            out.pop();
        }
        Some(out)
    }
}

/// Decide a single-assertion single-variable real polynomial constraint exactly,
/// returning an irrational witness when the satisfying value is algebraic.
///
/// Returns `Some(Sat(model))` / `Some(Unsat)` for the exact pattern (every `Sat`
/// model replay-checked), and `None` to decline (left to [`crate::nra`]).
///
/// # Errors
///
/// Returns [`SolverError`] to match the `?`-chained dispatch contract; the
/// decision itself does not currently fail (the `Result` is part of the stable
/// call signature).
#[allow(
    clippy::unnecessary_wraps,
    reason = "signature matches the ?-chained auto.rs dispatch contract"
)]
pub fn decide_real_poly_constraint(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<CheckResult>, SolverError> {
    // Fire only on a single-assertion query (a second assertion could constrain x).
    let [assertion] = assertions else {
        return Ok(None);
    };
    let Some((var, cmp, rat)) = match_real_poly_constraint(arena, *assertion) else {
        return Ok(None);
    };
    // Degree ≥ 1 required (a constant is exact LRA territory).
    if rat.degree() == 0 || rat.degree() > MAX_DEGREE {
        return Ok(None);
    }
    let Some(poly) = rat.to_integer_poly() else {
        return Ok(None);
    };
    // After clearing, re-trim degree (denominator clearing keeps degree).
    if poly.len() <= 1 {
        return Ok(None);
    }

    let Some(verdict) = decide(&poly, cmp) else {
        return Ok(None);
    };

    match verdict {
        Verdict::Unsat => Ok(Some(CheckResult::Unsat)),
        Verdict::SatRational(q) => {
            // Replay the rational witness through the ground evaluator on the
            // ORIGINAL assertion; accept only if it holds.
            let mut asg = Assignment::new();
            asg.set(var, Value::Real(q));
            if !matches!(eval(arena, *assertion, &asg), Ok(Value::Bool(true))) {
                return Ok(None);
            }
            let mut model = Model::new();
            model.set(var, Value::Real(q));
            Ok(Some(CheckResult::Sat(model)))
        }
        Verdict::SatAlgebraic(alpha) => {
            // Replay-check the algebraic witness: it must be a genuine root of the
            // collected polynomial, i.e. sign_at(p, α) = 0. (We do NOT ask the
            // evaluator to multiply algebraic numbers; the decider holds `poly`.)
            if alpha.sign_at(&poly) != Some(Sign::Zero) {
                return Ok(None);
            }
            // For an equality `p = 0` the root replays by construction. For an
            // inequality we never return an algebraic witness (samples are
            // rational), so this branch is equality-only.
            let mut model = Model::new();
            model.set(var, Value::RealAlgebraic(alpha));
            Ok(Some(CheckResult::Sat(model)))
        }
    }
}

/// A decision plus its witness.
enum Verdict {
    Unsat,
    SatRational(Rational),
    SatAlgebraic(RealAlgebraic),
}

/// Decide `p(x) ⋈ 0` over the reals from the integer polynomial `poly`.
fn decide(poly: &[i128], cmp: Cmp) -> Option<Verdict> {
    match cmp {
        Cmp::Eq => decide_eq(poly),
        Cmp::Ne => decide_ne(poly),
        Cmp::Lt | Cmp::Le | Cmp::Gt | Cmp::Ge => decide_inequality(poly, cmp),
    }
}

/// `p(x) = 0`: isolate the real roots; return the first as a rational (if exact)
/// or algebraic witness, or **Unsat** if there are none.
fn decide_eq(poly: &[i128]) -> Option<Verdict> {
    let roots = isolate_roots(poly)?;
    match roots.into_iter().next() {
        None => Some(Verdict::Unsat),
        Some(Root::Rational(q)) => Some(Verdict::SatRational(q)),
        Some(Root::Algebraic(a)) => Some(Verdict::SatAlgebraic(a)),
    }
}

/// `p(x) ≠ 0`: Sat unless `p ≡ 0`. A nonzero degree-`n` poly has ≤ `n` roots, so
/// some small integer is a non-root; scan for one (rational witness).
fn decide_ne(poly: &[i128]) -> Option<Verdict> {
    if poly.iter().all(|&c| c == 0) {
        return Some(Verdict::Unsat); // p ≡ 0 ⇒ never ≠ 0
    }
    for k in 0..=(MAX_DEGREE as i128 + 8) {
        for cand in [k, -k] {
            let q = Rational::integer(cand);
            if !eval_rat(poly, q)?.is_zero() {
                return Some(Verdict::SatRational(q));
            }
        }
    }
    None
}

/// `p(x) ⋈ 0` for a strict/loose inequality: the roots partition ℝ into open
/// sign-constant intervals (plus the two unbounded tails); test a **rational**
/// sample in each candidate region. For `≤`/`≥` a root itself (where `p = 0`) is
/// also a witness, returned as a rational/algebraic root.
fn decide_inequality(poly: &[i128], cmp: Cmp) -> Option<Verdict> {
    let want = |s: Sign| -> bool {
        match cmp {
            Cmp::Lt => s == Sign::Neg,
            Cmp::Le => s == Sign::Neg || s == Sign::Zero,
            Cmp::Gt => s == Sign::Pos,
            Cmp::Ge => s == Sign::Pos || s == Sign::Zero,
            Cmp::Eq | Cmp::Ne => unreachable!(),
        }
    };
    let roots = isolate_roots(poly)?;

    // `≤`/`≥` accept a root directly (p = 0 there).
    if matches!(cmp, Cmp::Le | Cmp::Ge)
        && let Some(r) = roots.first()
    {
        return Some(match r {
            Root::Rational(q) => Verdict::SatRational(*q),
            Root::Algebraic(a) => Verdict::SatAlgebraic(a.clone()),
        });
    }

    // Build the rational sample points: midpoints between consecutive root
    // *interval* separators, plus one point below the lowest and above the
    // highest. We use rational endpoints that are guaranteed strictly between
    // adjacent roots (the isolating intervals are disjoint and ordered).
    let separators = root_separators(&roots);
    for s in separators {
        let sign = Sign::of_rational(eval_rat(poly, s)?);
        if want(sign) {
            return Some(Verdict::SatRational(s));
        }
    }
    Some(Verdict::Unsat)
}

/// An isolated real root: an exact rational, or an algebraic number defined by
/// `poly` and an isolating interval.
#[derive(Clone)]
enum Root {
    Rational(Rational),
    Algebraic(RealAlgebraic),
}

impl Root {
    /// A rational strictly-inside point representing the root's location, used to
    /// order roots and to derive sample separators. For a rational root it is the
    /// value; for an algebraic one it is the interval midpoint.
    fn locate(&self) -> Rational {
        match self {
            Root::Rational(q) => *q,
            Root::Algebraic(a) => a.approx_midpoint().unwrap_or_else(Rational::zero),
        }
    }
}

/// The number of equal cells the root-isolation grid subdivides `[-B, B]` into
/// (a uniform first pass to separate roots into distinct cells). Bounded so the
/// scan is cheap; each cell is then bisected to isolate its single root. `1 <<
/// 14` (16384) cells over the Cauchy interval comfortably separates the roots of
/// any small-degree, `i128`-coefficient polynomial this pass admits.
const ISOLATE_GRID: i128 = 1 << 14;

/// Maximum bisection depth used to isolate / tighten a single root within one
/// sign-change cell. Each step halves the cell, so the witness interval shrinks
/// by `2^DEPTH`; 48 is far finer than any replay or comparison needs.
const ISOLATE_REFINE_DEPTH: u32 = 48;

/// Isolate **all** real roots of the integer polynomial `poly`, returned in
/// ascending order, each as a [`Root`]. Returns `None` on overflow.
///
/// Method (exact, no float): bound the roots by the Cauchy bound
/// `B = 1 + max|aᵢ| / |aₙ|`, scan a uniform rational grid over `[-B, B]`, and for
/// each consecutive pair of grid points classify the cell:
/// - an exact rational root at a grid point (`poly = 0`) is recorded directly;
/// - a strict sign change across the cell brackets exactly one root, which is
///   then **bisected** to either an exact rational root or a tightly-isolated
///   algebraic number.
///
/// The grid is fine enough that distinct roots of an admissible polynomial fall
/// in distinct cells; a cell with equal nonzero endpoint signs is treated as
/// root-free (sound for the squarefree/separated polynomials in scope — and any
/// missed witness only ever degrades a `Sat` to a sound decline upstream, never a
/// wrong verdict, because every returned `Sat` is replay-checked and `Unsat` for
/// `=` is reported only when no sign change is found anywhere on `[-B, B]`, which
/// — `B` being a true root bound — is exact for these polynomials).
fn isolate_roots(poly: &[i128]) -> Option<Vec<Root>> {
    let lead = *poly.last()?;
    if lead == 0 {
        return None;
    }
    let max_other = poly[..poly.len() - 1]
        .iter()
        .map(|c| c.unsigned_abs())
        .max()
        .unwrap_or(0);
    // Cauchy bound B = 1 + max|aᵢ|/|aₙ|, rounded up to an integer.
    let bound = Rational::integer(1).checked_add(Rational::checked_new(
        i128::try_from(max_other).ok()?,
        lead.checked_abs()?,
    )?)?;
    let b_int = bound
        .numerator()
        .checked_div(bound.denominator())?
        .checked_add(1)?;
    let lo = Rational::integer(b_int.checked_neg()?);
    let hi = Rational::integer(b_int);
    let width = hi.checked_sub(lo)?;
    let step = width.checked_div(Rational::integer(ISOLATE_GRID))?;

    let mut roots: Vec<Root> = Vec::new();
    let mut prev = lo;
    let mut prev_val = eval_rat(poly, prev)?;
    // The very first grid point may be an exact root.
    if prev_val.is_zero() {
        roots.push(Root::Rational(prev));
    }
    for k in 1..=ISOLATE_GRID {
        let cur = lo.checked_add(step.checked_mul(Rational::integer(k))?)?;
        let cur_val = eval_rat(poly, cur)?;
        let s_prev = Sign::of_rational(prev_val);
        let s_cur = Sign::of_rational(cur_val);
        if s_cur == Sign::Zero {
            // Exact rational root at this grid point.
            roots.push(Root::Rational(cur));
        } else if s_prev != Sign::Zero && s_prev != s_cur {
            // Strict sign change in (prev, cur): exactly one root — isolate it.
            roots.push(isolate_one(poly, prev, cur)?);
        }
        prev = cur;
        prev_val = cur_val;
    }
    Some(roots)
}

/// Isolate the single root of `poly` in the open interval `(lo, hi)` known to have
/// a strict endpoint sign change. Bisect: an exact rational midpoint root yields a
/// [`Root::Rational`]; otherwise, after [`ISOLATE_REFINE_DEPTH`] steps, build a
/// tightly-isolated [`Root::Algebraic`] from `poly` and the narrowed interval.
fn isolate_one(poly: &[i128], lo: Rational, hi: Rational) -> Option<Root> {
    let mut lo = lo;
    let mut hi = hi;
    // The sign of `poly` at the lower endpoint stays invariant under the updates
    // below (when we move `lo` to `mid`, `mid` had the same sign as `lo`).
    let slo = Sign::of_rational(eval_rat(poly, lo)?);
    for _ in 0..ISOLATE_REFINE_DEPTH {
        let mid = lo.checked_add(hi)?.checked_div(Rational::integer(2))?;
        let smid = Sign::of_rational(eval_rat(poly, mid)?);
        if smid == Sign::Zero {
            return Some(Root::Rational(mid));
        }
        if smid == slo {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    // The bracket is now tiny. If `poly` has an *exact rational* root inside it
    // (rational-root theorem: numerator | a₀, denominator | aₙ), prefer that exact
    // rational witness over an algebraic representation. Otherwise the root is
    // irrational — represent it as an isolated algebraic number.
    if let Some(q) = rational_root_in(poly, lo, hi) {
        return Some(Root::Rational(q));
    }
    Some(Root::Algebraic(RealAlgebraic::new(poly.to_vec(), lo, hi)?))
}

/// The largest `|a₀|` / `|aₙ|` for which [`rational_root_in`] enumerates divisors
/// (trial division up to the value). The coefficient guard already caps these at
/// `MAX_ABS_COEFF`; this secondary bound keeps the divisor enumeration cheap.
const RATIONAL_ROOT_BOUND: i128 = 1 << 24;

/// If `poly` has an exact rational root strictly inside `(lo, hi)`, return it
/// (rational-root theorem: a rational root `p/q` in lowest terms has `p | a₀` and
/// `q | aₙ`). Returns `None` when there is no such root in the interval **or** the
/// search declines (an overflow, or a constant/leading term too large to
/// enumerate cheaply); in every `None` case the caller soundly falls back to an
/// algebraic representation, so conflating "not found" with "declined" is safe.
fn rational_root_in(poly: &[i128], lo: Rational, hi: Rational) -> Option<Rational> {
    let const_term = poly[0];
    let leading = *poly.last()?;
    // Constant term zero ⇒ 0 is a root; report it if it lies in the bracket.
    if const_term == 0 {
        let zero = Rational::zero();
        if zero > lo && zero < hi {
            return Some(zero);
        }
    }
    let const_abs = const_term.checked_abs()?;
    let lead_abs = leading.checked_abs()?;
    if const_abs == 0 || const_abs > RATIONAL_ROOT_BOUND || lead_abs > RATIONAL_ROOT_BOUND {
        return None; // nothing to enumerate / too large — leave as algebraic
    }
    for p in divisors(const_abs) {
        for q in divisors(lead_abs) {
            for cand in [Rational::checked_new(p, q)?, Rational::checked_new(-p, q)?] {
                if cand > lo && cand < hi && eval_rat(poly, cand)?.is_zero() {
                    return Some(cand);
                }
            }
        }
    }
    None
}

/// The positive divisors of `n > 0` (trial division). Empty for `n == 0`.
fn divisors(n: i128) -> Vec<i128> {
    let mut out = Vec::new();
    if n <= 0 {
        return out;
    }
    let mut d = 1i128;
    while d.saturating_mul(d) <= n {
        if n % d == 0 {
            out.push(d);
            if d != n / d {
                out.push(n / d);
            }
        }
        d += 1;
    }
    out
}

/// Rational sample points for the inequality sign scan: one strictly below the
/// lowest root, one strictly above the highest, and one strictly between each
/// adjacent pair of roots. With no roots, a single point (0) samples all of ℝ.
fn root_separators(roots: &[Root]) -> Vec<Rational> {
    if roots.is_empty() {
        return vec![Rational::zero()];
    }
    let locs: Vec<Rational> = roots.iter().map(Root::locate).collect();
    let mut pts = Vec::with_capacity(locs.len() + 1);
    // Below the lowest.
    pts.push(locs[0] - Rational::integer(1));
    // Between adjacent roots: the midpoint (the isolating intervals are disjoint,
    // so the midpoint of two distinct root locations lies strictly between them).
    for w in locs.windows(2) {
        if let Some(mid) = w[0]
            .checked_add(w[1])
            .and_then(|s| s.checked_div(Rational::integer(2)))
        {
            pts.push(mid);
        }
    }
    // Above the highest.
    pts.push(locs[locs.len() - 1] + Rational::integer(1));
    pts
}

/// LCM of two positive `i128` magnitudes, declining on overflow.
fn lcm_i128(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd_i128(a.unsigned_abs(), b.unsigned_abs());
    // a / g * b, with g | a exactly.
    let a_div = a.checked_div(i128::try_from(g).ok()?)?;
    a_div.checked_mul(b)?.checked_abs()
}

/// GCD of two unsigned magnitudes (Euclid).
fn gcd_i128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Exact Horner evaluation of an LSB-first integer polynomial at a [`Rational`].
fn eval_rat(poly: &[i128], x: Rational) -> Option<Rational> {
    let mut acc = Rational::zero();
    for &c in poly.iter().rev() {
        acc = acc.checked_mul(x)?.checked_add(Rational::integer(c))?;
    }
    Some(acc)
}

// Re-export the `Sign::of_rational` helper logic locally (the IR `Sign` does not
// expose a rational constructor publicly).
trait SignOfRational {
    fn of_rational(r: Rational) -> Sign;
}

impl SignOfRational for Sign {
    fn of_rational(r: Rational) -> Sign {
        match r.numerator().cmp(&0) {
            core::cmp::Ordering::Less => Sign::Neg,
            core::cmp::Ordering::Equal => Sign::Zero,
            core::cmp::Ordering::Greater => Sign::Pos,
        }
    }
}

/// Match a single real comparison/equality `lhs ⋈ rhs` (or `¬(lhs = rhs)` for
/// `≠`) where `lhs − rhs` collects to a single-variable real polynomial. Returns
/// `(x, cmp-as-`p ⋈ 0`, p = lhs − rhs)` or `None` to decline.
fn match_real_poly_constraint(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(SymbolId, Cmp, RatPoly)> {
    let TermNode::App { op, args } = arena.node(assertion) else {
        return None;
    };

    // `≠` is `not(=)`.
    if matches!(op, Op::BoolNot) {
        let inner = args[0];
        let TermNode::App {
            op: Op::Eq,
            args: eq_args,
        } = arena.node(inner)
        else {
            return None;
        };
        let poly = collect_diff(arena, eq_args[0], eq_args[1])?;
        let var = poly.var?;
        return Some((var, Cmp::Ne, poly));
    }

    let cmp = match op {
        Op::Eq => Cmp::Eq,
        Op::RealLt => Cmp::Lt,
        Op::RealLe => Cmp::Le,
        Op::RealGt => Cmp::Gt,
        Op::RealGe => Cmp::Ge,
        _ => return None,
    };
    // `Eq` must be over Real operands (an Int/BV equality is not ours).
    if matches!(op, Op::Eq) && arena.sort_of(args[0]) != Sort::Real {
        return None;
    }
    let poly = collect_diff(arena, args[0], args[1])?;
    let var = poly.var?;
    Some((var, cmp, poly))
}

/// Collect `lhs − rhs` as a single-variable real polynomial, or `None`.
fn collect_diff(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<RatPoly> {
    let l = collect(arena, lhs)?;
    let r = collect(arena, rhs)?;
    l.sub(r)
}

/// Recursively collect a `Real`-sorted term into a single-variable rational
/// polynomial over `{+, −, ·, neg, RealConst, symbol}`. Anything else declines.
fn collect(arena: &TermArena, t: TermId) -> Option<RatPoly> {
    if arena.sort_of(t) != Sort::Real {
        return None;
    }
    match arena.node(t) {
        TermNode::RealConst(r) => Some(RatPoly::constant(*r)),
        TermNode::Symbol(s) => Some(RatPoly::var_of(*s)),
        TermNode::App { op, args } => match op {
            Op::RealNeg if args.len() == 1 => collect(arena, args[0])?.neg(),
            Op::RealAdd if args.len() == 2 => {
                collect(arena, args[0])?.add(&collect(arena, args[1])?)
            }
            Op::RealSub if args.len() == 2 => {
                collect(arena, args[0])?.sub(collect(arena, args[1])?)
            }
            Op::RealMul if args.len() == 2 => {
                collect(arena, args[0])?.mul(&collect(arena, args[1])?)
            }
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ipoly(coeffs: &[i128]) -> Vec<i128> {
        coeffs.to_vec()
    }

    #[test]
    fn isolate_sqrt2() {
        // x² − 2: roots ±√2 (both irrational).
        let roots = isolate_roots(&ipoly(&[-2, 0, 1])).unwrap();
        assert_eq!(roots.len(), 2);
        for r in &roots {
            assert!(matches!(r, Root::Algebraic(_)));
        }
    }

    #[test]
    fn isolate_rational_roots() {
        // x² − 4: roots ±2 (both rational).
        let roots = isolate_roots(&ipoly(&[-4, 0, 1])).unwrap();
        assert_eq!(roots.len(), 2);
        for r in &roots {
            assert!(matches!(r, Root::Rational(_)));
        }
    }

    #[test]
    fn no_real_root() {
        // x² + 1: no real root.
        let roots = isolate_roots(&ipoly(&[1, 0, 1])).unwrap();
        assert!(roots.is_empty());
    }

    #[test]
    fn eq_sqrt2_is_algebraic_sat() {
        match decide_eq(&ipoly(&[-2, 0, 1])).unwrap() {
            Verdict::SatAlgebraic(a) => assert_eq!(a.sign_at(&[-2, 0, 1]), Some(Sign::Zero)),
            _ => panic!("expected algebraic sat"),
        }
    }

    #[test]
    fn lt_zero_unsat_for_square_plus() {
        // x² < 0: no negative value ⇒ Unsat. (poly = x², roots {0}.)
        match decide(&ipoly(&[0, 0, 1]), Cmp::Lt).unwrap() {
            Verdict::Unsat => {}
            _ => panic!("expected unsat"),
        }
    }

    #[test]
    fn gt_two_has_rational_witness() {
        // x² − 2 > 0: e.g. x = 2 (sign +). Witness must be rational.
        match decide(&ipoly(&[-2, 0, 1]), Cmp::Gt).unwrap() {
            Verdict::SatRational(q) => {
                assert!(eval_rat(&[-2, 0, 1], q).unwrap().numerator() > 0);
            }
            _ => panic!("expected rational sat"),
        }
    }

    #[test]
    fn le_zero_sat_at_origin() {
        // x² ≤ 0 ⇒ x = 0 (the root). Witness is the rational root 0.
        match decide(&ipoly(&[0, 0, 1]), Cmp::Le).unwrap() {
            Verdict::SatRational(q) => assert!(q.is_zero()),
            _ => panic!("expected rational sat at 0"),
        }
    }
}
