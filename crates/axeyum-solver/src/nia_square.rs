//! Sound, bounded NIA capability: decide a single-variable integer **quadratic
//! constraint** `a·x² + b·x + c ⋈ 0` (one `Int` variable `x`, integer constants
//! `a ≠ 0`, `b`, `c`, and `⋈ ∈ {=, ≠, <, ≤, >, ≥}`) *exactly*.
//!
//! This generalizes the original single-square decider `x*x ⋈ c` (the `a = 1,
//! b = 0` subcase, which is still decided here verbatim) and closes the
//! hunt-flagged gap `int x*x = 2` → **Unsat** (`2` is not a perfect square),
//! which the bounded bit-blast width ladder and the real relaxation only ever
//! report as `Unknown`.
//!
//! # Scope (deliberately narrow — correctness over reach)
//!
//! The pass fires *only* when the **whole** query (after the dispatcher's
//! preprocessing) is exactly **one** assertion that normalizes to a comparison
//! between a single-variable integer polynomial of **degree exactly 2** and a
//! constant — i.e. `p(x) ⋈ q(x)` where `p − q` collects to `a·x² + b·x + c`
//! with `a ≠ 0`, integer coefficients, and `x` the only variable.
//!
//! Everything else declines (`None`), leaving `x` to the existing NIA dispatch:
//!
//! - more than one variable (`x² + y`, `x·y`),
//! - degree `> 2` (`x³`, `x²·x`),
//! - degree `< 2` after collection (linear / constant — exact LIA handles it),
//! - non-`Int` sort (a `Real` square is the NRA √ case),
//! - any operator outside `{+, −, ·, neg, const, var}` (e.g. `div`, `mod`,
//!   `abs`) — they could hide non-polynomial behavior,
//! - any coefficient (or intermediate product) that overflows the `i128`
//!   collection or the safe magnitude guard,
//! - any query with a number of assertions other than one (a second assertion
//!   could otherwise constrain `x`).
//!
//! A wrong `sat`/`unsat` is unacceptable; declining is always sound, and every
//! `Sat` is additionally **replay-checked** against the original assertion.
//!
//! # The math
//!
//! Normalize the comparison to `f(x) = a·x² + b·x + c ⋈ 0` (moving the
//! right-hand side across; `≠` is `¬(= 0)`; a constant on the left flips the
//! comparator). We always reduce the **downward** parabola `a < 0` to the
//! **upward** case by negating `f` *and* flipping `⋈` (e.g. `f < 0` with `a < 0`
//! becomes `−f > 0` with `−a > 0`). So below assume `a > 0`.
//!
//! Discriminant `D = b² − 4·a·c`. Real roots exist iff `D ≥ 0`; the vertex is at
//! `x* = −b/(2a)`, where `f` attains its (convex) minimum.
//!
//! - **`f = 0`** (equality): an *integer* root exists iff `D ≥ 0`, `D` is a
//!   perfect square (`s = isqrt(D)`, `s·s == D`), and `(−b + s)` or `(−b − s)`
//!   is divisible by `2a` (so a root `(−b ± s)/(2a)` is an integer). Sat with
//!   that witness, else Unsat.
//! - **`f ≠ 0`**: a degree-2 polynomial has at most 2 roots, so it is nonzero at
//!   all but ≤ 2 integers — **always Sat**. We exhibit a concrete non-root.
//! - **`f < 0`** / **`f ≤ 0`**: `f` is convex, so its minimum over the integers
//!   is at `⌊x*⌋` or `⌈x*⌉` (the two integers straddling the real vertex). Sat
//!   iff `min(f(⌊x*⌋), f(⌈x*⌉))` is `< 0` (resp. `≤ 0`). This needs **no
//!   irrational root**: we only evaluate `f` at integers. (Soundness: convexity
//!   ⇒ the integer minimizer is one of the two vertex neighbors; if no integer
//!   makes `f` negative, the global integer minimum is `≥ 0`.)
//! - **`f > 0`** / **`f ≥ 0`**: `f → +∞` as `x → ±∞`, so these are **always
//!   Sat**; a witness far from the vertex works, found by scanning outward and
//!   replay-checking. (For `≥`, even the vertex neighbors suffice when the
//!   minimum is `≥ 0`.)
//!
//! Every `Sat` returns a **replay-checked** witness model: the witness is set on
//! `x`, the *original* assertion is re-evaluated through the ground evaluator,
//! and the `Sat` is emitted only if it evaluates to `true`. Any internal logic
//! slip therefore degrades to a sound *decline*, never a wrong `sat`.

use axeyum_ir::{Assignment, Op, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{CheckResult, SolverError};
use crate::model::Model;

/// Above this magnitude for any of `|a|, |b|, |c|` the pass declines (returns
/// `None`) rather than risk `i128` overflow in `b²`, `4·a·c`, `isqrt`, or the
/// `f(k)` evaluations. `2^40` keeps `b² ≤ 2^80`, `4·a·c ≤ 2^82`, and (for the
/// witnesses we probe, `|x|` bounded by the search) `a·x² + b·x + c` far inside
/// `i128` (`≈ 2^127`). Larger coefficients are left to the existing NIA dispatch
/// (sound).
const MAX_ABS_COEFF: i128 = 1i128 << 40;

/// Outward scan bound (in integer steps from a vertex neighbor) for finding a
/// witness in the "always Sat" tail cases (`f > 0` / `f ≥ 0` / `f ≠ 0`). `f`
/// grows quadratically, so a handful of steps always clears any bounded gap, but
/// we cap the scan and *decline* if no witness replays — soundness over reach.
const TAIL_SCAN: i128 = 64;

/// The six integer comparison shapes the quadratic pass decides, oriented as
/// `f(x) ⋈ 0`.
#[derive(Clone, Copy)]
enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Cmp {
    /// Flip the comparator for the `a < 0` → `a > 0` reduction (negating `f`):
    /// `f ⋈ 0 ⟺ −f (flip ⋈) 0`. Equality / disequality are unchanged.
    fn flip(self) -> Self {
        match self {
            Cmp::Eq => Cmp::Eq,
            Cmp::Ne => Cmp::Ne,
            Cmp::Lt => Cmp::Gt,
            Cmp::Le => Cmp::Ge,
            Cmp::Gt => Cmp::Lt,
            Cmp::Ge => Cmp::Le,
        }
    }
}

/// Result of merging the variable identity of two operands: either the merged
/// (sole, possibly absent) variable, or a `Conflict` (two distinct variables),
/// which forces the collector to decline.
enum MergeVar {
    Ok(Option<SymbolId>),
    Conflict,
}

/// A single-variable integer polynomial of degree `≤ 2`: `c2·x² + c1·x + c0`.
/// `var` is the (sole) variable; `None` only when the polynomial is constant.
#[derive(Clone, Copy)]
struct Poly {
    var: Option<SymbolId>,
    c0: i128,
    c1: i128,
    c2: i128,
}

impl Poly {
    fn constant(n: i128) -> Self {
        Poly {
            var: None,
            c0: n,
            c1: 0,
            c2: 0,
        }
    }

    fn var_of(s: SymbolId) -> Self {
        Poly {
            var: Some(s),
            c0: 0,
            c1: 1,
            c2: 0,
        }
    }

    /// Merge the variable identity of two operands. Two distinct variables force
    /// a *decline* ([`MergeVar::Conflict`]); otherwise the merged (possibly
    /// `None`) variable is carried through.
    fn merge_var(a: Option<SymbolId>, b: Option<SymbolId>) -> MergeVar {
        match (a, b) {
            (None, v) | (v, None) => MergeVar::Ok(v),
            (Some(x), Some(y)) if x == y => MergeVar::Ok(Some(x)),
            _ => MergeVar::Conflict, // two different variables → not single-variable
        }
    }

    fn neg(self) -> Option<Self> {
        Some(Poly {
            var: self.var,
            c0: self.c0.checked_neg()?,
            c1: self.c1.checked_neg()?,
            c2: self.c2.checked_neg()?,
        })
    }

    fn add(self, other: Self) -> Option<Self> {
        let MergeVar::Ok(var) = Poly::merge_var(self.var, other.var) else {
            return None;
        };
        Some(Poly {
            var,
            c0: self.c0.checked_add(other.c0)?,
            c1: self.c1.checked_add(other.c1)?,
            c2: self.c2.checked_add(other.c2)?,
        })
    }

    fn sub(self, other: Self) -> Option<Self> {
        self.add(other.neg()?)
    }

    /// Multiply two degree-`≤ 2` polynomials, **declining** if the product would
    /// exceed degree 2 (a genuine cubic/quartic) or overflow `i128`.
    fn mul(self, other: Self) -> Option<Self> {
        // (a2 x² + a1 x + a0)·(b2 x² + b1 x + b0). The product exceeds degree 2 iff
        // some pair of terms with combined degree > 2 is nonzero:
        //   self.c2·other.c1 (deg 3), self.c2·other.c2 (deg 4), self.c1·other.c2 (deg 3).
        let degree_too_high =
            (self.c2 != 0 && (other.c1 != 0 || other.c2 != 0)) || (self.c1 != 0 && other.c2 != 0);
        if degree_too_high {
            return None;
        }
        // Surviving terms: x²·1, x·x, x·1, 1·x², 1·x, 1·1.
        let c0 = self.c0.checked_mul(other.c0)?;
        let c1 = self
            .c0
            .checked_mul(other.c1)?
            .checked_add(self.c1.checked_mul(other.c0)?)?;
        let c2 = self
            .c0
            .checked_mul(other.c2)?
            .checked_add(self.c2.checked_mul(other.c0)?)?
            .checked_add(self.c1.checked_mul(other.c1)?)?;
        let MergeVar::Ok(var) = Poly::merge_var(self.var, other.var) else {
            return None;
        };
        Some(Poly { var, c0, c1, c2 })
    }

    /// Evaluate `f(k)` exactly, declining on `i128` overflow.
    fn eval_at(&self, k: i128) -> Option<i128> {
        let k2 = k.checked_mul(k)?;
        let t2 = self.c2.checked_mul(k2)?;
        let t1 = self.c1.checked_mul(k)?;
        t2.checked_add(t1)?.checked_add(self.c0)
    }
}

/// Decides a single-assertion integer **quadratic constraint**
/// `a·x² + b·x + c ⋈ 0` exactly.
///
/// Returns `Some(Sat(model))` / `Some(Unsat)` for the exact pattern (every `Sat`
/// model replay-checked against the original assertion), and `None` for anything
/// outside it — multiple variables, degree `≠ 2`, a non-`Int` square, an
/// unsupported operator, a coefficient out of the safe range, or a query with
/// any number of assertions other than one. Declining is always sound.
///
/// # Errors
///
/// Returns [`SolverError`] to match the dispatcher's `?`-chained call site; the
/// decision itself does not currently fail (the `Result` is part of the stable
/// dispatch contract, kept for forward compatibility).
#[allow(
    clippy::unnecessary_wraps,
    reason = "signature matches the ?-chained auto.rs dispatch contract"
)]
pub fn decide_int_square_constraint(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<CheckResult>, SolverError> {
    // The pass fires only when the WHOLE query is exactly one assertion. A second
    // assertion could otherwise constrain `x` (e.g. `x*x = 4 ∧ x = 2`), so we must
    // not decide the polynomial in isolation — decline and let the NIA dispatch see
    // all constraints together.
    let [assertion] = assertions else {
        return Ok(None);
    };
    let Some((var, cmp, poly)) = match_quadratic_constraint(arena, *assertion) else {
        return Ok(None);
    };

    // Degree must be exactly 2 with a nonzero leading coefficient (`a ≠ 0`).
    // Degree < 2 (linear / constant) is exact LIA territory — decline.
    let (a, b, c) = (poly.c2, poly.c1, poly.c0);
    if a == 0 {
        return Ok(None);
    }

    // Overflow guard: only decide coefficients whose magnitude keeps `b²`, `4ac`,
    // `isqrt`, and the probed `f(k)` within `i128`. Larger ones decline (sound).
    if a.abs() >= MAX_ABS_COEFF || b.abs() >= MAX_ABS_COEFF || c.abs() >= MAX_ABS_COEFF {
        return Ok(None);
    }

    let Some(verdict) = decide(cmp, poly) else {
        return Ok(None);
    };
    match verdict {
        Verdict::Unsat => Ok(Some(CheckResult::Unsat)),
        Verdict::SatWith(witness) => {
            // Replay-check: set `x := witness` and evaluate the ORIGINAL assertion
            // through the ground evaluator. The `Sat` is sound only if it holds.
            let mut assignment = Assignment::new();
            assignment.set(var, Value::Int(witness));
            if !matches!(eval(arena, *assertion, &assignment), Ok(Value::Bool(true))) {
                // The witness did not satisfy the original assertion. This must not
                // happen for the case analysis above, but soundness comes first:
                // decline rather than emit an unchecked `sat`.
                return Ok(None);
            }
            let mut model = Model::new();
            model.set(var, Value::Int(witness));
            Ok(Some(CheckResult::Sat(model)))
        }
    }
}

/// The decision for one shape, carrying the concrete witness for `Sat`.
enum Verdict {
    Unsat,
    SatWith(i128),
}

/// Exact case analysis for `f(x) ⋈ 0` (see the module docs). Returns `None` to
/// **decline** (any case we cannot make airtight, e.g. an overflow in the
/// witness search), which the caller turns into a sound `None` dispatch.
fn decide(cmp: Cmp, poly: Poly) -> Option<Verdict> {
    // Reduce the downward parabola to the upward case: `f ⋈ 0 ⟺ −f (flip) 0`,
    // so the analysis below may assume `a > 0`.
    if poly.c2 < 0 {
        return decide(cmp.flip(), poly.neg()?);
    }
    let (a, b, c) = (poly.c2, poly.c1, poly.c0);
    debug_assert!(a > 0);

    match cmp {
        Cmp::Eq => decide_eq(poly, a, b, c),
        // A degree-2 polynomial is zero at ≤ 2 integers, so `f ≠ 0` is always
        // Sat: scan for a concrete non-root.
        Cmp::Ne => find_witness(&poly, |v| v != 0),
        // `f < 0` (a > 0, convex): Sat iff some integer makes f negative; the
        // minimizer is a vertex neighbor.
        Cmp::Lt => decide_min_negative(poly, a, b, /* strict */ true),
        Cmp::Le => decide_min_negative(poly, a, b, /* strict */ false),
        // `f > 0` / `f ≥ 0` (a > 0): f → +∞, always Sat. Find a witness.
        Cmp::Gt => find_witness(&poly, |v| v > 0),
        Cmp::Ge => find_witness(&poly, |v| v >= 0),
    }
}

/// `f(x) = 0` with `a > 0`: integer root iff `D = b² − 4ac` is a non-negative
/// perfect square and some `(−b ± s)/(2a)` is an integer.
fn decide_eq(poly: Poly, a: i128, b: i128, c: i128) -> Option<Verdict> {
    let b2 = b.checked_mul(b)?;
    let four_ac = 4i128.checked_mul(a)?.checked_mul(c)?;
    let disc = b2.checked_sub(four_ac)?;
    if disc < 0 {
        return Some(Verdict::Unsat); // no real root
    }
    let s = isqrt(disc);
    if s.checked_mul(s)? != disc {
        return Some(Verdict::Unsat); // irrational roots → no integer root
    }
    let two_a = 2i128.checked_mul(a)?;
    // Try both `(−b + s)` and `(−b − s)`; either divisible by 2a gives a root.
    for num in [(-b).checked_add(s)?, (-b).checked_sub(s)?] {
        if num % two_a == 0 {
            let root = num / two_a;
            // Replay belt-and-braces: confirm f(root) == 0 exactly.
            if poly.eval_at(root)? == 0 {
                return Some(Verdict::SatWith(root));
            }
        }
    }
    Some(Verdict::Unsat)
}

/// `f < 0` (`strict`) or `f ≤ 0` over the integers, with `a > 0` (convex). The
/// integer minimum is at a vertex neighbor `⌊x*⌋` or `⌈x*⌉`, `x* = −b/(2a)`. Sat
/// iff that minimum clears the threshold.
fn decide_min_negative(poly: Poly, a: i128, b: i128, strict: bool) -> Option<Verdict> {
    let two_a = 2i128.checked_mul(a)?;
    // x* = −b / (2a). The two straddling integers are floor and ceil of this
    // rational; with `two_a > 0`, floor-div in Rust rounds toward −∞ only for
    // exact non-negative numerators, so compute floor/ceil explicitly.
    let neg_b = b.checked_neg()?;
    let floor = floor_div(neg_b, two_a)?;
    let ceil = ceil_div(neg_b, two_a)?;
    // Evaluate at both straddling integers (they coincide when x* is integral).
    let mut best: Option<(i128, i128)> = None; // (value, witness)
    for k in [floor, ceil] {
        let v = poly.eval_at(k)?;
        match best {
            Some((bv, _)) if bv <= v => {}
            _ => best = Some((v, k)),
        }
    }
    let (min_val, witness) = best?;
    let sat = if strict { min_val < 0 } else { min_val <= 0 };
    if sat {
        Some(Verdict::SatWith(witness))
    } else {
        Some(Verdict::Unsat)
    }
}

/// Find an integer witness satisfying `pred(f(k))`, scanning vertex neighbors and
/// then outward (both directions). Returns `Some(SatWith)` on success or `None`
/// to decline if no witness is found within the bounded scan (sound — these are
/// only ever called for genuinely-always-Sat shapes, where the scan succeeds
/// immediately for `a > 0`; a miss can only come from an overflow, where
/// declining is correct).
fn find_witness(poly: &Poly, pred: impl Fn(i128) -> bool) -> Option<Verdict> {
    let a = poly.c2;
    let b = poly.c1;
    let two_a = 2i128.checked_mul(a)?;
    let center = if two_a == 0 {
        0
    } else {
        floor_div(b.checked_neg()?, two_a)?
    };
    // Probe the vertex and a symmetric outward band. For `a > 0` and a "tail"
    // predicate (`> 0`, `≥ 0`, `≠ 0`) at least one of these always satisfies.
    for d in 0..=TAIL_SCAN {
        for k in [center.checked_add(d)?, center.checked_sub(d)?] {
            if let Some(v) = poly.eval_at(k)
                && pred(v)
            {
                return Some(Verdict::SatWith(k));
            }
        }
    }
    None
}

/// Floor of `n / d` for `d > 0` (rounds toward −∞), overflow-safe.
fn floor_div(n: i128, d: i128) -> Option<i128> {
    debug_assert!(d > 0);
    let q = n.checked_div(d)?;
    let r = n.checked_rem(d)?;
    if r < 0 { q.checked_sub(1) } else { Some(q) }
}

/// Ceil of `n / d` for `d > 0` (rounds toward +∞), overflow-safe.
fn ceil_div(n: i128, d: i128) -> Option<i128> {
    debug_assert!(d > 0);
    let q = n.checked_div(d)?;
    let r = n.checked_rem(d)?;
    if r > 0 { q.checked_add(1) } else { Some(q) }
}

/// The binary-search ceiling for [`isqrt`]: `2^51`. The caller guards the
/// coefficients below `2^40`, so the discriminant `D = b² − 4ac` stays below
/// `2^83`, giving `⌊√D⌋ < 2^42 ≤ 2^51 = HI`; every probed `mid` is `≤ 2^51`,
/// keeping `mid*mid ≤ 2^102` (and the final `(r+1)*(r+1) < 2^102`) well within
/// `i128` (`≈ 2^127`).
const ISQRT_HI: i128 = 1i128 << 51;

/// Integer square root of `c ≥ 0`: the unique `r ≥ 0` with
/// `r*r ≤ c < (r+1)*(r+1)`.
///
/// Overflow-safe by construction: the binary search is capped at [`ISQRT_HI`]
/// (`2^51`), keeping every `mid*mid` (and the final `r*r` / `(r+1)*(r+1)`) far
/// inside `i128` for any discriminant the coefficient guard admits.
///
/// # Panics
///
/// Panics on `c < 0` (the callers only ever pass `c ≥ 0`).
fn isqrt(c: i128) -> i128 {
    assert!(c >= 0, "isqrt requires c >= 0");
    if c < 2 {
        return c; // isqrt(0)=0, isqrt(1)=1
    }
    let (mut lo, mut hi) = (0i128, ISQRT_HI);
    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        let sq = mid * mid; // safe: mid ≤ 2^51 ⇒ sq ≤ 2^102 < i128::MAX
        match sq.cmp(&c) {
            std::cmp::Ordering::Equal => return mid,
            std::cmp::Ordering::Less => lo = mid + 1,
            std::cmp::Ordering::Greater => hi = mid - 1,
        }
    }
    // `hi` is now the largest value with hi*hi ≤ c.
    hi
}

/// Matches a single integer comparison/equality `lhs ⋈ rhs` (or `¬(lhs = rhs)`
/// for `≠`) where `lhs − rhs` collects to a single-variable integer polynomial.
/// Returns `(x_symbol, comparison-as-`f ⋈ 0`, polynomial f = lhs − rhs)` or
/// `None` to decline.
fn match_quadratic_constraint(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(SymbolId, Cmp, Poly)> {
    let TermNode::App { op, args } = arena.node(assertion) else {
        return None;
    };

    // `≠` is `not(=)`: peel a single Boolean negation over an `Eq`.
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
        let var = poly.var?; // must actually contain the variable
        return Some((var, Cmp::Ne, poly));
    }

    if !matches!(op, Op::Eq | Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe) {
        return None;
    }
    let cmp = match op {
        Op::Eq => Cmp::Eq,
        Op::IntLt => Cmp::Lt,
        Op::IntLe => Cmp::Le,
        Op::IntGt => Cmp::Gt,
        Op::IntGe => Cmp::Ge,
        _ => return None,
    };
    // `lhs ⋈ rhs ⟺ (lhs − rhs) ⋈ 0`, so collect `f = lhs − rhs` and keep the
    // comparator as `f ⋈ 0`.
    let poly = collect_diff(arena, args[0], args[1])?;
    let var = poly.var?;
    Some((var, cmp, poly))
}

/// Collect `lhs − rhs` into a single-variable degree-`≤ 2` polynomial, or `None`
/// to decline.
fn collect_diff(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<Poly> {
    let l = collect(arena, lhs)?;
    let r = collect(arena, rhs)?;
    l.sub(r)
}

/// Recursively collect an `Int`-sorted term into a single-variable degree-`≤ 2`
/// polynomial over `{+, −, ·, neg, const, var}`. Any other operator, a non-`Int`
/// term, a second variable, degree `> 2`, or an arithmetic overflow declines.
fn collect(arena: &TermArena, t: TermId) -> Option<Poly> {
    // Only collect Int-sorted terms (a Real square is out of scope).
    if arena.sort_of(t) != axeyum_ir::Sort::Int {
        return None;
    }
    match arena.node(t) {
        TermNode::IntConst(n) => Some(Poly::constant(*n)),
        TermNode::Symbol(s) => Some(Poly::var_of(*s)),
        TermNode::App { op, args } => match op {
            Op::IntNeg if args.len() == 1 => collect(arena, args[0])?.neg(),
            Op::IntAdd if args.len() == 2 => collect(arena, args[0])?.add(collect(arena, args[1])?),
            Op::IntSub if args.len() == 2 => collect(arena, args[0])?.sub(collect(arena, args[1])?),
            Op::IntMul if args.len() == 2 => collect(arena, args[0])?.mul(collect(arena, args[1])?),
            // div / mod / abs / anything else: not a polynomial we model.
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{Poly, ceil_div, floor_div, isqrt};

    #[test]
    fn isqrt_perfect_and_nonperfect() {
        assert_eq!(isqrt(0), 0);
        assert_eq!(isqrt(1), 1);
        assert_eq!(isqrt(2), 1);
        assert_eq!(isqrt(3), 1);
        assert_eq!(isqrt(4), 2);
        assert_eq!(isqrt(8), 2);
        assert_eq!(isqrt(9), 3);
        assert_eq!(isqrt(1_000_000), 1000);
        assert_eq!(isqrt(999_999), 999);
        let big = 1i128 << 80;
        let r = isqrt(big);
        assert!(r * r <= big && (r + 1) * (r + 1) > big);
    }

    #[test]
    fn floor_ceil_div_signs() {
        assert_eq!(floor_div(7, 2), Some(3));
        assert_eq!(ceil_div(7, 2), Some(4));
        assert_eq!(floor_div(-7, 2), Some(-4));
        assert_eq!(ceil_div(-7, 2), Some(-3));
        assert_eq!(floor_div(6, 2), Some(3));
        assert_eq!(ceil_div(6, 2), Some(3));
        assert_eq!(floor_div(-6, 2), Some(-3));
        assert_eq!(ceil_div(-6, 2), Some(-3));
    }

    #[test]
    fn poly_mul_degree_guard() {
        // `tests` is a child module, so it may use the private `Poly` fields. Build
        // x, x², x³-would-be directly (var = None is irrelevant to the degree guard).
        let x = Poly {
            var: None,
            c0: 0,
            c1: 1,
            c2: 0,
        };
        // x · x = x² (degree 2, ok)
        let x2 = x.mul(x).unwrap();
        assert_eq!((x2.c0, x2.c1, x2.c2), (0, 0, 1));
        // x² · x would be degree 3 → decline.
        assert!(x2.mul(x).is_none());
        // (x + 1)² = x² + 2x + 1.
        let xp1 = Poly {
            var: None,
            c0: 1,
            c1: 1,
            c2: 0,
        };
        let sq = xp1.mul(xp1).unwrap();
        assert_eq!((sq.c0, sq.c1, sq.c2), (1, 2, 1));
    }
}
