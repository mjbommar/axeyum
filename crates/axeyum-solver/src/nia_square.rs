//! Sound, bounded NIA capability: decide a single-variable integer
//! **polynomial constraint** over one `Int` variable `x` *exactly*.
//!
//! Two layers, both correctness-first:
//!
//! 1. **Degree ≤ 2 (the quadratic decider):** any comparison
//!    `a·x² + b·x + c ⋈ 0` with `⋈ ∈ {=, ≠, <, ≤, >, ≥}` is decided exactly via
//!    the discriminant / convexity analysis below. This generalizes the original
//!    single-square decider `x*x ⋈ c` (the `a = 1, b = 0` subcase, still decided
//!    here verbatim) and closes the gap `int x*x = 2` → **Unsat** (`2` is not a
//!    perfect square), which the bounded bit-blast width ladder and the real
//!    relaxation only ever report as `Unknown`.
//!
//! 2. **Degree ≥ 3 (the rational-root decider, equality and safe `≠` only):**
//!    for a single assertion `p(x) = 0` (or `0 = p(x)`) of degree ≥ 3, every
//!    *integer* root of `aₙxⁿ + … + a₁x + a₀` must, by the **Rational Root
//!    Theorem**, divide the constant term `a₀` (the `q = 1` specialization for an
//!    integer-valued unknown). So if `a₀ = 0`, `x = 0` is a root (Sat); otherwise
//!    we enumerate the divisors of `|a₀|` (both signs), evaluate `p` at each by
//!    overflow-safe Horner, and return **Sat** with the first root or **Unsat**
//!    when *every* divisor has been checked and none is a root — an exact verdict.
//!    Disequality `p(x) ≠ 0` of degree ≥ 3 is Sat unless `p` is the zero
//!    polynomial (a degree-`n` poly has ≤ `n` roots), exhibited by a bounded scan
//!    for a non-root; *inequalities* of degree ≥ 3 (`<`, `≤`, `>`, `≥`) have no
//!    exact bounded method here and **decline** (left to NIA).
//!
//! # Scope (deliberately narrow — correctness over reach)
//!
//! The pass fires *only* when the **whole** query (after the dispatcher's
//! preprocessing) is exactly **one** assertion that normalizes to a comparison
//! between a single-variable integer polynomial and a constant — i.e.
//! `p(x) ⋈ q(x)` where `p − q` collects to a single-variable integer polynomial
//! with `x` the only variable.
//!
//! Everything else declines (`None`), leaving `x` to the existing NIA dispatch:
//!
//! - more than one variable (`x² + y`, `x·y`, `x³ + y`),
//! - degree `< 1` after collection (constant — exact LIA handles it),
//! - degree `≥ 3` with a comparator other than `=` / `≠` (an inequality — no
//!   exact bounded method here),
//! - degree `> 64` (an absurd degree — bound the divisor / Horner work),
//! - non-`Int` sort (a `Real` square is the NRA √ case),
//! - any operator outside `{+, −, ·, neg, const, var}` (e.g. `div`, `mod`,
//!   `abs`) — they could hide non-polynomial behavior,
//! - any coefficient (or intermediate product) that overflows the `i128`
//!   collection or the safe magnitude guard,
//! - for the rational-root path: a constant term `|a₀|` at or above the safe
//!   magnitude bound (`2^40`) whose divisor enumeration would be costly, **or**
//!   any overflow during Horner evaluation,
//! - any query with a number of assertions other than one (a second assertion
//!   could otherwise constrain `x`).
//!
//! A wrong `sat`/`unsat` is unacceptable; declining is always sound, and every
//! `Sat` is additionally **replay-checked** against the original assertion.
//!
//! # The math (degree ≤ 2)
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

/// Above this magnitude for any coefficient the pass declines (returns `None`)
/// rather than risk `i128` overflow in `b²`, `4·a·c`, `isqrt`, the `f(k)`
/// evaluations, or (for the rational-root path) the divisor enumeration / Horner
/// evaluation. `2^40` keeps `b² ≤ 2^80`, `4·a·c ≤ 2^82`, and the probed
/// witnesses far inside `i128` (`≈ 2^127`). It is also the bound on `|a₀|` for
/// divisor enumeration: at `2^40` the trial-division loop is `~2^20` iterations
/// worst case, comfortably bounded. Larger coefficients are left to the existing
/// NIA dispatch (sound).
const MAX_ABS_COEFF: i128 = 1i128 << 40;

/// Outward scan bound (in integer steps from a vertex neighbor) for finding a
/// witness in the "always Sat" tail cases (`f > 0` / `f ≥ 0` / `f ≠ 0`). `f`
/// grows quadratically, so a handful of steps always clears any bounded gap, but
/// we cap the scan and *decline* if no witness replays — soundness over reach.
const TAIL_SCAN: i128 = 64;

/// Maximum polynomial degree the pass will collect / decide. Beyond this we
/// decline (sound): an absurd degree (deeply nested products) would otherwise
/// let collection and Horner evaluation do unbounded work. 64 is far above any
/// realistic single-variable polynomial goal.
const MAX_DEGREE: usize = 64;

/// Bounded scan for a degree-`≥ 3` `≠` non-root witness. A degree-`n` polynomial
/// has at most `n` integer roots, so among `MAX_DEGREE + 2` distinct integers at
/// least one is a non-root; the scan is centered on 0 and walks outward. We cap
/// it and *decline* on a miss (only reachable via overflow) — soundness first.
const NE_SCAN: i128 = (MAX_DEGREE as i128) + 8;

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

/// A single-variable integer polynomial `coeffs[n]·xⁿ + … + coeffs[1]·x +
/// coeffs[0]`, stored coefficient-indexed-by-degree (LSB first). `var` is the
/// (sole) variable; `None` only when the polynomial is constant. The vector is
/// always kept non-empty (`coeffs[0]` exists) and trailing zeros are trimmed so
/// the last entry is the genuine leading coefficient (except for the zero
/// polynomial, kept as `[0]`).
#[derive(Clone)]
struct Poly {
    var: Option<SymbolId>,
    coeffs: Vec<i128>,
}

impl Poly {
    fn constant(n: i128) -> Self {
        Poly {
            var: None,
            coeffs: vec![n],
        }
    }

    fn var_of(s: SymbolId) -> Self {
        Poly {
            var: Some(s),
            coeffs: vec![0, 1],
        }
    }

    /// Coefficient of `xⁱ` (`0` past the stored length).
    fn coeff(&self, i: usize) -> i128 {
        self.coeffs.get(i).copied().unwrap_or(0)
    }

    /// Constant term `c0` (coefficient of `x⁰`).
    fn c0(&self) -> i128 {
        self.coeff(0)
    }

    /// Linear coefficient `c1` (coefficient of `x¹`).
    fn c1(&self) -> i128 {
        self.coeff(1)
    }

    /// Quadratic coefficient `c2` (coefficient of `x²`).
    fn c2(&self) -> i128 {
        self.coeff(2)
    }

    /// Degree: the highest index with a nonzero coefficient, or `0` for a
    /// constant (including the zero polynomial). Trailing zeros are trimmed on
    /// construction, so this is `coeffs.len() − 1` once non-empty and trimmed.
    fn degree(&self) -> usize {
        self.coeffs.len().saturating_sub(1)
    }

    /// Trim trailing zero coefficients so the leading entry is genuine; keep at
    /// least one entry (`[0]` for the zero polynomial).
    fn trim(mut self) -> Self {
        while self.coeffs.len() > 1 && *self.coeffs.last().unwrap() == 0 {
            self.coeffs.pop();
        }
        self
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
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for &c in &self.coeffs {
            coeffs.push(c.checked_neg()?);
        }
        Some(Poly {
            var: self.var,
            coeffs,
        })
    }

    fn add(self, other: &Self) -> Option<Self> {
        let MergeVar::Ok(var) = Poly::merge_var(self.var, other.var) else {
            return None;
        };
        let len = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = Vec::with_capacity(len);
        for i in 0..len {
            coeffs.push(self.coeff(i).checked_add(other.coeff(i))?);
        }
        Some(Poly { var, coeffs }.trim())
    }

    fn sub(self, other: Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    /// Multiply two single-variable integer polynomials, **declining** on an
    /// `i128` overflow or a product degree exceeding [`MAX_DEGREE`].
    fn mul(self, other: &Self) -> Option<Self> {
        let MergeVar::Ok(var) = Poly::merge_var(self.var, other.var) else {
            return None;
        };
        // Degree of the product = deg(self) + deg(other) (zero polys handled by
        // the trailing-zero trim afterward). Bound the work up front.
        let prod_len = self.coeffs.len() + other.coeffs.len() - 1;
        if prod_len > MAX_DEGREE + 1 {
            return None;
        }
        let mut coeffs = vec![0i128; prod_len];
        for (i, &a) in self.coeffs.iter().enumerate() {
            if a == 0 {
                continue;
            }
            for (j, &b) in other.coeffs.iter().enumerate() {
                if b == 0 {
                    continue;
                }
                let term = a.checked_mul(b)?;
                coeffs[i + j] = coeffs[i + j].checked_add(term)?;
            }
        }
        Some(Poly { var, coeffs }.trim())
    }

    /// Evaluate `f(k)` exactly by Horner's method, declining on `i128` overflow.
    fn eval_at(&self, k: i128) -> Option<i128> {
        let mut acc = 0i128;
        // Horner: acc = ((cₙ·k + cₙ₋₁)·k + … )·k + c₀.
        for &c in self.coeffs.iter().rev() {
            acc = acc.checked_mul(k)?.checked_add(c)?;
        }
        Some(acc)
    }

    /// `true` iff every coefficient is within the safe magnitude guard.
    fn coeffs_in_guard(&self) -> bool {
        self.coeffs.iter().all(|c| c.abs() < MAX_ABS_COEFF)
    }
}

/// Decides a single-assertion integer **polynomial constraint** `p(x) ⋈ 0`
/// exactly: the quadratic discriminant/convexity analysis for degree ≤ 2 and the
/// rational-root theorem for degree ≥ 3 equality (and safe `≠`).
///
/// Returns `Some(Sat(model))` / `Some(Unsat)` for the exact pattern (every `Sat`
/// model replay-checked against the original assertion), and `None` for anything
/// outside it — multiple variables, a constant (degree 0), a degree-`≥ 3`
/// inequality, an absurd degree, a non-`Int` square, an unsupported operator, a
/// coefficient out of the safe range, or a query with any number of assertions
/// other than one. Declining is always sound.
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
    let Some((var, cmp, poly)) = match_poly_constraint(arena, *assertion) else {
        return Ok(None);
    };

    // Degree must be ≥ 1: a constant (degree 0) is exact LIA territory — decline.
    let degree = poly.degree();
    if degree == 0 || degree > MAX_DEGREE {
        return Ok(None);
    }

    // Overflow guard: only decide coefficients whose magnitude keeps the quadratic
    // arithmetic and the Horner evaluations within `i128`. Larger ones decline.
    if !poly.coeffs_in_guard() {
        return Ok(None);
    }

    let verdict = if degree <= 2 {
        decide_quadratic(cmp, &poly)
    } else {
        decide_high_degree(cmp, &poly)
    };
    let Some(verdict) = verdict else {
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

/// Exact case analysis for the degree-`≤ 2` constraint `f(x) ⋈ 0` (see the
/// module docs). Returns `None` to **decline** (any case we cannot make
/// airtight, e.g. an overflow in the witness search).
fn decide_quadratic(cmp: Cmp, poly: &Poly) -> Option<Verdict> {
    // Reduce the downward parabola to the upward case: `f ⋈ 0 ⟺ −f (flip) 0`,
    // so the analysis below may assume `a > 0`.
    if poly.c2() < 0 {
        return decide_quadratic(cmp.flip(), &poly.clone().neg()?);
    }
    let (a, b, c) = (poly.c2(), poly.c1(), poly.c0());
    debug_assert!(a > 0);

    match cmp {
        Cmp::Eq => decide_eq(poly, a, b, c),
        // A degree-2 polynomial is zero at ≤ 2 integers, so `f ≠ 0` is always
        // Sat: scan for a concrete non-root.
        Cmp::Ne => find_witness(poly, |v| v != 0),
        // `f < 0` (a > 0, convex): Sat iff some integer makes f negative; the
        // minimizer is a vertex neighbor.
        Cmp::Lt => decide_min_negative(poly, a, b, /* strict */ true),
        Cmp::Le => decide_min_negative(poly, a, b, /* strict */ false),
        // `f > 0` / `f ≥ 0` (a > 0): f → +∞, always Sat. Find a witness.
        Cmp::Gt => find_witness(poly, |v| v > 0),
        Cmp::Ge => find_witness(poly, |v| v >= 0),
    }
}

/// Exact decision for a degree-`≥ 3` constraint via the **Rational Root
/// Theorem**. Only `=` (and the safe `≠`) are decided; inequalities decline.
///
/// For `p(x) = 0` (`a₀` the constant term):
/// - `a₀ = 0` ⇒ `x = 0` is a root ⇒ Sat (witness 0).
/// - else every integer root divides `a₀`; enumerate the divisors of `|a₀|`
///   (both signs), evaluate `p` (overflow-safe Horner) at each, and return Sat
///   on the first root or Unsat when none of them is a root.
///
/// For `p(x) ≠ 0`: Sat unless `p ≡ 0` (degree ≥ 3 here, so `p` is non-zero by
/// construction) — exhibit a bounded-scan non-root.
fn decide_high_degree(cmp: Cmp, poly: &Poly) -> Option<Verdict> {
    match cmp {
        Cmp::Eq => decide_high_degree_eq(poly),
        Cmp::Ne => {
            // A degree-n polynomial has ≤ n integer roots, so some integer in any
            // (n+1)-sized set is a non-root. Scan outward from 0.
            for d in 0..=NE_SCAN {
                for k in [d, -d] {
                    if let Some(v) = poly.eval_at(k)
                        && v != 0
                    {
                        return Some(Verdict::SatWith(k));
                    }
                }
            }
            None // unreachable except via overflow → decline (sound)
        }
        // Inequalities of degree ≥ 3 have no exact bounded method here: decline.
        Cmp::Lt | Cmp::Le | Cmp::Gt | Cmp::Ge => None,
    }
}

/// `p(x) = 0`, degree ≥ 3, via the rational root theorem. See
/// [`decide_high_degree`].
fn decide_high_degree_eq(poly: &Poly) -> Option<Verdict> {
    let a0 = poly.c0();
    // `a₀ = 0` ⇒ x = 0 is a root (every term has a factor of x).
    if a0 == 0 {
        // Confirm by exact evaluation (belt-and-braces; p(0) = a₀ = 0).
        if poly.eval_at(0)? == 0 {
            return Some(Verdict::SatWith(0));
        }
        return None;
    }

    // Magnitude guard: |a₀| must be within the safe bound so divisor enumeration
    // is cheap and overflow-free. (The coefficient guard already ensures this,
    // but assert it locally for the divisor-count bound.)
    let a0_abs = a0.checked_abs()?;
    if a0_abs >= MAX_ABS_COEFF {
        return None;
    }

    // Enumerate the positive divisors d of |a₀| by trial division up to √|a₀|,
    // testing both signs of d and of its cofactor. Any integer root must be such
    // a ±divisor, so the first one that zeroes `p` is a witness.
    let mut d = 1i128;
    while d.checked_mul(d)? <= a0_abs {
        if a0_abs % d == 0 {
            let cofactor = a0_abs / d;
            for cand in divisor_candidates(d, cofactor) {
                if poly.eval_at(cand)? == 0 {
                    return Some(Verdict::SatWith(cand));
                }
            }
        }
        d = d.checked_add(1)?;
    }
    // Every divisor checked, none a root, a₀ ≠ 0, no overflow ⇒ exact Unsat.
    Some(Verdict::Unsat)
}

/// The (at most four) signed divisor candidates contributed by a divisor pair
/// `(d, cofactor)` of `|a₀|`: `±d` and `±cofactor`. De-duplicated.
fn divisor_candidates(d: i128, cofactor: i128) -> impl Iterator<Item = i128> {
    let mut cands = vec![d, -d];
    if cofactor != d {
        cands.push(cofactor);
        cands.push(-cofactor);
    }
    cands.into_iter()
}

/// `f(x) = 0` with `a > 0`, degree ≤ 2: integer root iff `D = b² − 4ac` is a
/// non-negative perfect square and some `(−b ± s)/(2a)` is an integer.
fn decide_eq(poly: &Poly, a: i128, b: i128, c: i128) -> Option<Verdict> {
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
fn decide_min_negative(poly: &Poly, a: i128, b: i128, strict: bool) -> Option<Verdict> {
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
    let a = poly.c2();
    let b = poly.c1();
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
fn match_poly_constraint(arena: &TermArena, assertion: TermId) -> Option<(SymbolId, Cmp, Poly)> {
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

/// Collect `lhs − rhs` into a single-variable polynomial, or `None` to decline.
fn collect_diff(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<Poly> {
    let l = collect(arena, lhs)?;
    let r = collect(arena, rhs)?;
    l.sub(r)
}

/// Recursively collect an `Int`-sorted term into a single-variable polynomial
/// over `{+, −, ·, neg, const, var}`. Any other operator, a non-`Int` term, a
/// second variable, a degree past [`MAX_DEGREE`], or an arithmetic overflow
/// declines.
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
            Op::IntAdd if args.len() == 2 => {
                collect(arena, args[0])?.add(&collect(arena, args[1])?)
            }
            Op::IntSub if args.len() == 2 => collect(arena, args[0])?.sub(collect(arena, args[1])?),
            Op::IntMul if args.len() == 2 => {
                collect(arena, args[0])?.mul(&collect(arena, args[1])?)
            }
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
    fn poly_mul_and_degree() {
        // `tests` is a child module, so it may build `Poly` directly. Use the
        // public-within-module constructors / arithmetic.
        let x = Poly {
            var: None,
            coeffs: vec![0, 1],
        };
        // x · x = x² (degree 2).
        let x2 = x.clone().mul(&x).unwrap();
        assert_eq!(x2.coeffs, vec![0, 0, 1]);
        assert_eq!(x2.degree(), 2);
        // x² · x = x³ (degree 3, now allowed up to MAX_DEGREE).
        let x3 = x2.clone().mul(&x).unwrap();
        assert_eq!(x3.coeffs, vec![0, 0, 0, 1]);
        assert_eq!(x3.degree(), 3);
        // (x + 1)² = x² + 2x + 1.
        let xp1 = Poly {
            var: None,
            coeffs: vec![1, 1],
        };
        let sq = xp1.clone().mul(&xp1).unwrap();
        assert_eq!(sq.coeffs, vec![1, 2, 1]);
        assert_eq!((sq.c0(), sq.c1(), sq.c2()), (1, 2, 1));
    }

    #[test]
    fn horner_eval_matches_naive() {
        // p(x) = x³ − 6x² + 11x − 6, roots 1,2,3.
        let p = Poly {
            var: None,
            coeffs: vec![-6, 11, -6, 1],
        };
        assert_eq!(p.eval_at(0), Some(-6));
        assert_eq!(p.eval_at(1), Some(0));
        assert_eq!(p.eval_at(2), Some(0));
        assert_eq!(p.eval_at(3), Some(0));
        assert_eq!(p.eval_at(4), Some(6));
    }

    #[test]
    fn trim_drops_trailing_zeros() {
        let p = Poly {
            var: None,
            coeffs: vec![1, 2, 0, 0],
        }
        .trim();
        assert_eq!(p.coeffs, vec![1, 2]);
        assert_eq!(p.degree(), 1);
        // Zero polynomial collapses to [0], degree 0.
        let z = Poly {
            var: None,
            coeffs: vec![0, 0, 0],
        }
        .trim();
        assert_eq!(z.coeffs, vec![0]);
        assert_eq!(z.degree(), 0);
    }
}
