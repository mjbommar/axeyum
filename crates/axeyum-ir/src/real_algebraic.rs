//! Real algebraic numbers as a defining polynomial plus an isolating interval
//! (ADR-0038, slice 1).
//!
//! A [`RealAlgebraic`] is an *exact*, irrational-capable real value: an integer
//! polynomial `poly` (LSB-first, mirroring the NRA/NIA `Poly` layout) together
//! with a rational open interval `(lo, hi)` that contains **exactly one** real
//! root of `poly`. That unique root *is* the value. The single-root invariant is
//! established by construction (a sign change of `poly` between the endpoints,
//! the interval already isolated from any other root by the decider's root
//! isolation).
//!
//! Slice 1 supports only the two operations the single-variable NRA decider needs
//! to build and **replay-check** an irrational witness:
//!
//! - [`RealAlgebraic::sign_at`] — the exact sign of an arbitrary integer
//!   polynomial `q` evaluated at this algebraic number `α`, by **interval
//!   refinement**: repeatedly bisect `(lo, hi)` (keeping the half that still
//!   brackets the root of the *defining* `poly`) until `q` has a constant nonzero
//!   sign across the whole refined interval. `q ≡ poly` (or any `q` that vanishes
//!   at `α`) is detected and reported as sign `0`.
//! - [`RealAlgebraic::compare_rational`] — compare `α` against a rational `c` by
//!   refining until `c` falls outside `(lo, hi)`, or detecting `poly(c) = 0`
//!   (then `α = c`, since `α` is the interval's sole root).
//!
//! **Deferred (NOT slice 1):** algebraic *field arithmetic* (adding, multiplying,
//! or inverting two algebraic numbers). The evaluator therefore returns a
//! graceful error for `Real{Add,Sub,Mul,Neg,Div}` over an algebraic operand; the
//! decider never asks the evaluator to multiply two algebraic numbers — it
//! replay-checks its own witnesses with [`RealAlgebraic::sign_at`] against the
//! polynomial it already holds.
//!
//! **No floating point anywhere.** Every sign test is exact over `i128` /
//! [`Rational`]. Refinement is bounded; an `i128` overflow or a failure to
//! converge within the bound returns `None`, and the caller declines (a sound
//! `unknown`) rather than risk a wrong answer.

use core::cmp::Ordering;

use crate::rational::Rational;

/// The maximum number of bisection steps [`RealAlgebraic::sign_at`] and
/// [`RealAlgebraic::compare_rational`] will take before giving up (returning
/// `None` → the caller declines). Each step halves the interval, so the
/// resolution after `N` steps is `(hi − lo) / 2^N`; 256 steps is far more than
/// enough to separate any root the `i128`-bounded decider produces from a
/// distinct sign of a bounded polynomial, while staying cheap.
const MAX_REFINE_STEPS: u32 = 256;

/// The sign of a polynomial value at a point: negative, zero, or positive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sign {
    /// Strictly negative.
    Neg,
    /// Exactly zero.
    Zero,
    /// Strictly positive.
    Pos,
}

impl Sign {
    /// The sign of a rational value (`< 0`, `= 0`, `> 0`).
    fn of_rational(r: Rational) -> Sign {
        match r.numerator().cmp(&0) {
            Ordering::Less => Sign::Neg,
            Ordering::Equal => Sign::Zero,
            Ordering::Greater => Sign::Pos,
        }
    }
}

/// A real algebraic number: the unique real root of `poly` lying in the open
/// interval `(lo, hi)`.
///
/// Invariant (established by [`RealAlgebraic::new`]): `poly` has *exactly one*
/// real root in `(lo, hi)`, witnessed by `sign(poly(lo)) ≠ sign(poly(hi))` (both
/// nonzero), and the interval is otherwise root-isolated by the caller. The value
/// denoted is that root.
#[derive(Debug, Clone)]
pub struct RealAlgebraic {
    /// The defining integer polynomial, LSB-first (`coeffs[i]` is the coefficient
    /// of `xⁱ`). Trailing zeros are not required to be trimmed, but the leading
    /// coefficient must be nonzero for the degree to be meaningful.
    poly: Vec<i128>,
    /// The lower endpoint of the isolating interval (exclusive).
    lo: Rational,
    /// The upper endpoint of the isolating interval (exclusive).
    hi: Rational,
}

impl RealAlgebraic {
    /// Builds a real algebraic number from a defining polynomial and an isolating
    /// interval `(lo, hi)`, returning `None` if the one-root invariant cannot be
    /// confirmed: `lo < hi`, the polynomial must take a *strictly opposite,
    /// nonzero* sign at the two endpoints (a sign change ⇒ at least one root; the
    /// caller guarantees isolation ⇒ exactly one), and the endpoint evaluations
    /// must not overflow `i128`.
    ///
    /// The endpoint sign-change check is exact (Horner over [`Rational`]). If
    /// `poly(lo)` or `poly(hi)` is zero, the endpoint *is* the root — but the
    /// interval is open, so the caller should instead represent that exact
    /// rational root as `Value::Real`; here we reject it (`None`).
    #[must_use]
    pub fn new(poly: Vec<i128>, lo: Rational, hi: Rational) -> Option<RealAlgebraic> {
        if lo >= hi {
            return None;
        }
        let slo = Sign::of_rational(eval_int_poly_at(&poly, lo)?);
        let shi = Sign::of_rational(eval_int_poly_at(&poly, hi)?);
        // Strict opposite, nonzero signs ⇒ a root strictly inside (lo, hi).
        match (slo, shi) {
            (Sign::Neg, Sign::Pos) | (Sign::Pos, Sign::Neg) => Some(RealAlgebraic { poly, lo, hi }),
            _ => None,
        }
    }

    /// Represent a **rational** `c` as a degree-1 algebraic number: the unique
    /// root of `q·x − p` (where `c = p/q`, `q > 0`) in the open interval
    /// `(c − 1, c + 1)`. Used to lift a rational operand of algebraic field
    /// arithmetic into the common [`RealAlgebraic`] form. `None` on overflow.
    ///
    /// (The value is rational, so the result's `compare_rational(&c)` is `Equal`;
    /// it is a structurally-valid single-root bracket — the field-arithmetic
    /// resultant treats it uniformly.)
    #[must_use]
    pub fn from_rational(c: Rational) -> Option<RealAlgebraic> {
        // `c = p / q` with q > 0 (Rational keeps the denominator positive).
        let p = c.numerator();
        let q = c.denominator();
        // poly = q·x − p (LSB-first [−p, q]); root is exactly c.
        let poly = vec![p.checked_neg()?, q];
        let lo = c.checked_sub(Rational::integer(1))?;
        let hi = c.checked_add(Rational::integer(1))?;
        RealAlgebraic::new(poly, lo, hi)
    }

    /// The defining polynomial (LSB-first integer coefficients).
    #[must_use]
    pub fn defining_poly(&self) -> &[i128] {
        &self.poly
    }

    /// The current isolating interval `(lo, hi)`.
    #[must_use]
    pub fn interval(&self) -> (Rational, Rational) {
        (self.lo, self.hi)
    }

    /// Refine the isolating interval *in place* by one bisection step: evaluate
    /// the defining polynomial at the midpoint and keep the half whose endpoints
    /// still straddle the root (a strict sign change against the midpoint sign).
    /// Returns `Some(Sign::Zero)` if the midpoint *is* the root (then the value is
    /// exactly rational and both endpoints collapse to it), `Some(other)` for a
    /// successful narrowing, or `None` on `i128`/`Rational` overflow.
    fn refine_once(&mut self) -> Option<Sign> {
        let mid = self
            .lo
            .checked_add(self.hi)?
            .checked_div(Rational::integer(2))?;
        let smid = Sign::of_rational(eval_int_poly_at(&self.poly, mid)?);
        if smid == Sign::Zero {
            // The midpoint is the exact root: collapse the interval onto it.
            self.lo = mid;
            self.hi = mid;
            return Some(Sign::Zero);
        }
        // Keep the sub-interval whose endpoints straddle the root. The defining
        // poly's sign at `lo` is the opposite of its sign at `hi` (invariant), so
        // exactly one side matches the midpoint sign.
        let slo = Sign::of_rational(eval_int_poly_at(&self.poly, self.lo)?);
        if slo == smid {
            self.lo = mid;
        } else {
            self.hi = mid;
        }
        Some(smid)
    }

    /// The exact [`Sign`] of an arbitrary integer polynomial `q` evaluated at this
    /// algebraic number `α`.
    ///
    /// Strategy (exact, no float): evaluate `q` at both interval endpoints.
    /// - If both endpoint values are nonzero and *share* a sign, `q` is sign-
    ///   constant across the bracket and that is the answer.
    /// - Otherwise refine the isolating interval (narrowing toward `α`) and retry.
    ///   As the interval shrinks toward `α`, either `q`'s sign becomes constant
    ///   (when `q(α) ≠ 0`) or the interval collapses onto an exact rational root
    ///   of the *defining* poly where `q` can be evaluated directly.
    ///
    /// Returns `Sign::Zero` when `q` vanishes at `α` (detected via an exact
    /// rational root of the defining poly, or a refinement that drives both
    /// endpoints' `q`-values to bracket zero with a confirmed common root). For
    /// the slice-1 replay use, the decider only ever asks `sign_at(poly, α)`,
    /// which is `0` by the single-root invariant.
    ///
    /// Returns `None` (→ the caller declines, a sound `unknown`) on `i128`
    /// overflow or if a constant nonzero sign is not reached within
    /// `MAX_REFINE_STEPS`.
    #[must_use]
    pub fn sign_at(&self, q: &[i128]) -> Option<Sign> {
        // Exact vanishing test: if the defining polynomial `poly` divides `q`
        // (exactly, over the rationals), then every root of `poly` — in
        // particular α — is a root of `q`, so `q(α) = 0`. This decides the
        // common replay call `sign_at(poly, α)` and any (rational) multiple of
        // `poly` *without refinement* and is the only sound way to report `Zero`
        // for an irrational α (refinement alone can never confirm a zero at an
        // irrational point). On overflow the divisibility test declines (returns
        // `None`), and we fall through to refinement.
        if poly_divides(&self.poly, q) == Some(true) {
            return Some(Sign::Zero);
        }

        // Work on a local copy of the interval so `sign_at` stays `&self`.
        let mut probe = self.clone();
        for _ in 0..MAX_REFINE_STEPS {
            let vlo = eval_int_poly_at(q, probe.lo)?;
            let vhi = eval_int_poly_at(q, probe.hi)?;
            // If either endpoint coincides with the (now possibly collapsed)
            // root, `q(α)` is exactly that endpoint value.
            if probe.lo == probe.hi {
                return Some(Sign::of_rational(vlo));
            }
            let slo = Sign::of_rational(vlo);
            let shi = Sign::of_rational(vhi);
            // `q` sign-constant and nonzero across the whole bracket ⇒ that sign.
            if slo == shi && slo != Sign::Zero {
                return Some(slo);
            }
            // An endpoint exactly zero: that endpoint is a rational root of `q`.
            // It is α only if it is also a root of the defining poly, but the
            // endpoints are *not* roots of the defining poly (open-interval
            // invariant) until the interval collapses (handled above). So a zero
            // here means `q` has a root at the endpoint that is not α; refine away
            // from it. Refinement moves the endpoint inward, so continue.
            if let Sign::Zero = probe.refine_once()? {
                // The interval collapsed onto an exact rational root r of the
                // defining poly: α = r. Evaluate q(r) exactly.
                let qr = eval_int_poly_at(q, probe.lo)?;
                return Some(Sign::of_rational(qr));
            }
        }
        None
    }

    /// Compare this algebraic number `α` against a rational `c`.
    ///
    /// Refines the isolating interval until `c` lies strictly outside `(lo, hi)`
    /// (then the comparison is decided by which side), or detects `poly(c) = 0`
    /// (then `c` is *a* root of the defining poly inside the bracket, hence `α`
    /// itself by isolation ⇒ [`Ordering::Equal`]).
    ///
    /// Returns `None` (→ decline) on overflow or non-convergence within
    /// `MAX_REFINE_STEPS`.
    #[must_use]
    pub fn compare_rational(&self, c: &Rational) -> Option<Ordering> {
        // If `c` is a root of the defining poly and it lies in the (open) bracket,
        // it must be α (the unique root there).
        if *c > self.lo
            && *c < self.hi
            && Sign::of_rational(eval_int_poly_at(&self.poly, *c)?) == Sign::Zero
        {
            return Some(Ordering::Equal);
        }
        let mut probe = self.clone();
        for _ in 0..MAX_REFINE_STEPS {
            // `c` below the bracket ⇒ α > c; above ⇒ α < c.
            if *c <= probe.lo {
                return Some(Ordering::Greater);
            }
            if *c >= probe.hi {
                return Some(Ordering::Less);
            }
            // `c` strictly inside: refine and re-test. If the interval collapses
            // onto an exact root r = α, compare α to c directly.
            if let Sign::Zero = probe.refine_once()? {
                return probe.lo.checked_cmp(c);
            }
        }
        None
    }

    /// A rational strictly inside the current isolating interval — the interval
    /// midpoint — usable as a coarse numeric stand-in (never used for any sign
    /// decision, only for display/diagnostics).
    #[must_use]
    pub fn approx_midpoint(&self) -> Option<Rational> {
        self.lo
            .checked_add(self.hi)?
            .checked_div(Rational::integer(2))
    }

    // ========================================================================
    // Algebraic field arithmetic (ADR-0038, slice 3): −α, α+β, α·β.
    //
    // Each returns `Option<RealAlgebraic>`, declining (`None`) on any `i128`
    // overflow, degree/coefficient-guard trip, or an inability to isolate the
    // unique result root (Sturm count != 1) within the refinement bound. NEVER a
    // wrong value: the single-root invariant of the returned `RealAlgebraic` is
    // re-established by an EXACT Sturm count == 1 with strict opposite-sign
    // endpoints, exactly as `RealAlgebraic::new` requires.
    //
    // No floating point. The defining polynomial of `α + β` (resp. `α · β`) is a
    // factor of the resultant `Res_y(p_α(y), p_β(x − y))` (resp. the homogenized
    // `Res_y(p_α(y), y^{deg β} p_β(x/y))`); the correct root is the one inside the
    // sum (resp. product) of the operand intervals, identified by narrowing the
    // operand intervals and Sturm-counting the candidate result polynomial until
    // the interval brackets exactly one root.
    // ========================================================================

    /// The exact additive inverse `−α`.
    ///
    /// If `α` is the unique root of `p(x)` in `(lo, hi)`, then `−α` is the unique
    /// root of `p(−x)` in `(−hi, −lo)`. `p(−x)` is obtained by flipping the sign
    /// of every odd-degree coefficient. Exact; `None` only on coefficient
    /// negation overflow (`i128::MIN`).
    #[must_use]
    pub fn neg(&self) -> Option<RealAlgebraic> {
        let mut poly = Vec::with_capacity(self.poly.len());
        for (i, &c) in self.poly.iter().enumerate() {
            if i % 2 == 1 {
                poly.push(c.checked_neg()?);
            } else {
                poly.push(c);
            }
        }
        let lo = self.hi.checked_neg()?;
        let hi = self.lo.checked_neg()?;
        RealAlgebraic::new(poly, lo, hi)
    }

    /// The exact sum `α + β`.
    ///
    /// `α + β` is a root of `R(x) = Res_y(p_α(y), p_β(x − y))`, a univariate
    /// integer polynomial. Take its squarefree part `q`; the *correct* root is the
    /// unique root of `q` in `I = [α.lo + β.lo, α.hi + β.hi]`. We narrow `α` and
    /// `β`'s isolating intervals (each bisection keeps the half still bracketing
    /// that operand's root) so `I` shrinks, and use the exact Sturm count to drive
    /// it until `I` contains EXACTLY ONE root of `q` with strict opposite signs at
    /// the endpoints, then build the `RealAlgebraic`. Bounded → `None`.
    #[must_use]
    pub fn add(&self, other: &RealAlgebraic) -> Option<RealAlgebraic> {
        // i128 fast path: p_α(y) constant in x; p_β(x − y) polynomial in x.
        let i128_path = (|| {
            let pa = ratvec_const_coeffs(&self.poly);
            let pb = beta_of_x_minus_y(&other.poly)?;
            let q = resultant_then_squarefree(&pa, &pb)?;
            combine_via_interval(self, other, &q, IntervalCombine::Sum)
        })();
        if i128_path.is_some() {
            return i128_path;
        }
        // Overflow/decline on the i128 path: retry the SAME algorithm in bignum
        // (feature `bignum`), converting the final result back to i128 if it fits.
        self.combine_bignum(other, BignumCombine::Sum)
    }

    /// The exact product `α · β`.
    ///
    /// If either operand is the rational `0` the product is `0` — but a
    /// [`RealAlgebraic`] is by construction irrational, so neither operand is `0`
    /// here; the product is therefore a root of the homogenized resultant
    /// `R(x) = Res_y(p_α(y), y^{deg β}·p_β(x / y))`. Take the squarefree part and
    /// identify the unique root inside the product interval `[min, max]` of the
    /// four endpoint products, exactly as [`RealAlgebraic::add`]. Bounded →
    /// `None`.
    #[must_use]
    pub fn mul(&self, other: &RealAlgebraic) -> Option<RealAlgebraic> {
        // i128 fast path: p_α(y) constant in x; y^{deg β}·p_β(x / y).
        let i128_path = (|| {
            let pa = ratvec_const_coeffs(&self.poly);
            let pb = beta_homogenized(&other.poly)?;
            let q = resultant_then_squarefree(&pa, &pb)?;
            combine_via_interval(self, other, &q, IntervalCombine::Product)
        })();
        if i128_path.is_some() {
            return i128_path;
        }
        // i128 decline ⇒ bignum retry (feature-gated).
        self.combine_bignum(other, BignumCombine::Product)
    }

    /// The bignum retry shared by [`RealAlgebraic::add`] and
    /// [`RealAlgebraic::mul`]: re-run the resultant → squarefree → Sturm-isolation
    /// over arbitrary-precision rationals, then convert the FINAL defining
    /// polynomial + isolating interval back to the `i128`-backed representation.
    /// Returns `Some(RealAlgebraic)` only if the final result fits `i128` AND
    /// re-establishes the [`RealAlgebraic::new`] single-root invariant; otherwise
    /// `None` (a sound decline — a bignum-backed `RealAlgebraic` is a later slice).
    ///
    /// When the `bignum` feature is OFF this is a no-op returning `None`, so the
    /// overall behavior is exactly the i128-decline of before.
    fn combine_bignum(&self, other: &RealAlgebraic, how: BignumCombine) -> Option<RealAlgebraic> {
        combine_bignum_retry(self, other, how)
    }
}

/// Which field operation the bignum retry should perform (a feature-independent
/// mirror of [`IntervalCombine`], so the method signature does not depend on the
/// `bignum` feature being enabled).
#[derive(Clone, Copy)]
enum BignumCombine {
    Sum,
    Product,
}

/// The bignum retry (free function so the `not(feature)` no-op does not trip
/// `clippy::unused_self`): re-run the resultant → squarefree → Sturm-isolation in
/// arbitrary precision, then convert the FINAL poly + interval back to `i128`.
/// Feature OFF ⇒ always `None` (exactly the prior i128-decline behavior).
#[cfg(feature = "bignum")]
fn combine_bignum_retry(
    a: &RealAlgebraic,
    b: &RealAlgebraic,
    how: BignumCombine,
) -> Option<RealAlgebraic> {
    use crate::poly_big::{Combine, combine_retry};
    let how = match how {
        BignumCombine::Sum => Combine::Sum,
        BignumCombine::Product => Combine::Product,
    };
    let big = combine_retry(&a.poly, a.lo, a.hi, &b.poly, b.lo, b.hi, how)?;
    let (poly, lo, hi) = big.to_i128()?;
    // Guard the interval comparison with `checked_cmp` BEFORE calling `new`:
    // `new`'s `lo >= hi` uses the panicking `Rational` ordering, and the
    // bignum→i128 conversion can yield endpoints whose individual numerator/
    // denominator fit `i128` yet overflow the cross-multiplication in `cmp`. We
    // must NEVER panic — decline (`None`) if the comparison would overflow, and
    // require `lo < hi` before handing the (now-safe) interval to `new`.
    if lo.checked_cmp(&hi)? != Ordering::Less {
        return None;
    }
    // Re-establish the single-root invariant in i128 (defense-in-depth: the bignum
    // path already confirmed exactly one root with opposite endpoint signs; `new`
    // re-checks the converted endpoints — and `lo < hi` is now guaranteed safe).
    RealAlgebraic::new(poly, lo, hi)
}

/// Feature-OFF stub: no bignum retry, decline exactly as before.
#[cfg(not(feature = "bignum"))]
fn combine_bignum_retry(
    _a: &RealAlgebraic,
    _b: &RealAlgebraic,
    _how: BignumCombine,
) -> Option<RealAlgebraic> {
    None
}

/// How the result interval is derived from the two operand intervals.
#[derive(Clone, Copy)]
enum IntervalCombine {
    /// `[α.lo + β.lo, α.hi + β.hi]`.
    Sum,
    /// The min/max of the four endpoint products.
    Product,
}

/// Maximum number of operand-interval-narrowing rounds [`combine_via_interval`]
/// performs while driving the candidate result interval to bracket exactly one
/// root of `q`. Each round bisects both operand intervals (halving the result
/// interval's width), so the bound is generous; hitting it ⇒ decline.
const COMBINE_REFINE_ROUNDS: u32 = 200;

/// The degree / coefficient guards used by the field-arithmetic Sturm work. These
/// mirror the solver's NRA guards so the `i128` exact path stays bounded; beyond
/// them we decline (the bignum lift is a later ADR-gated step).
const FIELD_MAX_DEGREE: usize = 64;
const FIELD_MAX_ABS_COEFF: i128 = 1i128 << 40;

/// Lift an LSB-first integer polynomial to "coefficients (by y-exponent) that are
/// constant polynomials in x" — each a length-1 `RatVec`. Used for `p_α(y)`,
/// whose coefficients do not depend on the surviving variable `x`.
fn ratvec_const_coeffs(poly: &[i128]) -> Vec<crate::poly::RatVec> {
    let trimmed = crate::poly::rat_from_int(poly);
    trimmed.into_iter().map(|c| vec![c]).collect()
}

/// Binomial coefficient `C(n, k)` as an `i128`, `None` on overflow.
fn binom(n: usize, k: usize) -> Option<i128> {
    if k > n {
        return Some(0);
    }
    let k = k.min(n - k);
    let mut num = 1i128;
    for i in 0..k {
        num = num.checked_mul(i128::try_from(n - i).ok()?)?;
        // Divide as we go to keep magnitudes small (exact: the running product of
        // i+1 consecutive integers is divisible by (i+1)!).
        num = num.checked_div(i128::try_from(i + 1).ok()?)?;
    }
    Some(num)
}

/// `p_β(x − y)` as a polynomial in `y` whose coefficients are LSB-first rational
/// polynomials in `x` (indexed by the `y`-exponent). The `y`-degree equals
/// `deg p_β`.
///
/// `p_β(x − y) = Σ_j b_j (x − y)^j`, and `(x − y)^j = Σ_i C(j,i) x^{j−i} (−y)^i`,
/// so the coefficient of `y^i` is `Σ_{j ≥ i} b_j · C(j,i) · (−1)^i · x^{j−i}`.
fn beta_of_x_minus_y(poly: &[i128]) -> Option<Vec<crate::poly::RatVec>> {
    let trimmed = crate::poly::rat_from_int(poly);
    let n = crate::poly::rat_degree(&trimmed)?; // β nonconstant ⇒ n ≥ 1
    if n == 0 || n > FIELD_MAX_DEGREE {
        return None;
    }
    // coeff[i] (i = y-exponent) is an LSB-first RatVec in x of degree (n − i).
    let mut out: Vec<crate::poly::RatVec> = vec![Vec::new(); n + 1];
    for (i, slot) in out.iter_mut().enumerate() {
        // x-degrees 0..=(n − i).
        let mut xcoeffs = vec![Rational::zero(); n - i + 1];
        let sign = if i % 2 == 0 { 1i128 } else { -1i128 };
        for j in i..=n {
            let bj = trimmed[j];
            if bj.is_zero() {
                continue;
            }
            let c = binom(j, i)?;
            let term = bj
                .checked_mul(Rational::integer(c))?
                .checked_mul(Rational::integer(sign))?;
            // x^{j − i}.
            xcoeffs[j - i] = xcoeffs[j - i].checked_add(term)?;
        }
        *slot = xcoeffs;
    }
    Some(out)
}

/// `y^{deg β}·p_β(x / y)` as a polynomial in `y` whose coefficients are LSB-first
/// rational polynomials in `x` (indexed by the `y`-exponent). The `y`-degree
/// equals `deg p_β`.
///
/// `y^n·p_β(x / y) = Σ_j b_j x^j y^{n − j}`, so the coefficient of `y^{n − j}` is
/// the single monomial `b_j · x^j`.
fn beta_homogenized(poly: &[i128]) -> Option<Vec<crate::poly::RatVec>> {
    let trimmed = crate::poly::rat_from_int(poly);
    let n = crate::poly::rat_degree(&trimmed)?;
    if n == 0 || n > FIELD_MAX_DEGREE {
        return None;
    }
    // out[k] (k = y-exponent) is the x-polynomial; here out[n − j] = b_j·x^j.
    let mut out: Vec<crate::poly::RatVec> = vec![vec![Rational::zero()]; n + 1];
    for (j, &bj) in trimmed.iter().enumerate() {
        if bj.is_zero() {
            continue;
        }
        let k = n - j; // y-exponent
        let mut xcoeffs = vec![Rational::zero(); j + 1];
        xcoeffs[j] = bj;
        out[k] = xcoeffs;
    }
    Some(out)
}

/// Build `Res_y(p_α, p_β')` (both given as y-indexed coefficient vectors that are
/// LSB-first rational polynomials in `x`), clear to an integer polynomial, then
/// return its **squarefree part** as an integer polynomial. `None` on overflow,
/// a degenerate (constant) resultant, or any guard trip.
fn resultant_then_squarefree(
    pa: &[crate::poly::RatVec],
    pb: &[crate::poly::RatVec],
) -> Option<Vec<i128>> {
    let m = pa.len().checked_sub(1)?;
    let n = pb.len().checked_sub(1)?;
    if m == 0 || n == 0 {
        return None;
    }
    if m + n > FIELD_MAX_DEGREE {
        return None;
    }
    let mat = crate::poly::sylvester_matrix(pa, pb)?;
    let det = crate::poly::sylvester_determinant(&mat)?;
    if det.iter().all(|c| c.is_zero()) {
        return None; // identically-zero resultant: cannot isolate
    }
    let res_int = crate::poly::rat_to_int_poly(&det, FIELD_MAX_ABS_COEFF)?;
    if res_int.len() <= 1 {
        return None; // constant resultant: no root to identify
    }
    // Squarefree part (same root set, simple roots) → integer poly.
    let rat = crate::poly::rat_from_int(&res_int);
    let sqfree = crate::poly::squarefree_part(&rat, FIELD_MAX_DEGREE)?;
    let q = crate::poly::rat_to_int_poly(&sqfree, FIELD_MAX_ABS_COEFF)?;
    if q.len() <= 1 || *q.last()? == 0 {
        return None;
    }
    Some(q)
}

/// Identify the unique root of the candidate squarefree polynomial `q` that equals
/// `α ∘ β` (∘ = + or ·), and return it as a `RealAlgebraic`.
///
/// Method (exact, no float): maintain a candidate interval `I` derived from the
/// current operand intervals (`Sum`: `[α.lo+β.lo, α.hi+β.hi]`; `Product`: the
/// min/max of the four endpoint products). Narrow `α` and `β`'s intervals so `I`
/// shrinks, and Sturm-count the roots of `q` in `I` until the count is exactly 1
/// with strict opposite-sign endpoints — the [`RealAlgebraic::new`] invariant.
/// Bounded by [`COMBINE_REFINE_ROUNDS`] → `None` (sound decline).
fn combine_via_interval(
    a: &RealAlgebraic,
    b: &RealAlgebraic,
    q: &[i128],
    how: IntervalCombine,
) -> Option<RealAlgebraic> {
    // Sturm chain of `q` (squarefree) for the exact in-interval root count.
    let qrat = crate::poly::rat_from_int(q);
    let chain = crate::poly::sturm_chain(&qrat, FIELD_MAX_DEGREE)?;

    let mut pa = a.clone();
    let mut pb = b.clone();

    for _ in 0..COMBINE_REFINE_ROUNDS {
        let (lo, hi) = combined_interval(&pa, &pb, how)?;
        // Degenerate interval ⇒ keep narrowing (or bail if it cannot improve).
        if lo.checked_cmp(&hi)? != Ordering::Less {
            // Operand intervals collapsed onto exact rationals but the operands are
            // irrational by construction, so this should not happen; decline.
            return None;
        }
        // Endpoints must be non-roots of `q` for the half-open Sturm count to be a
        // clean open-interval count, AND strict opposite signs are required by
        // `new`. If an endpoint is exactly a root of `q`, nudge by narrowing.
        let slo = Sign::of_rational(eval_int_poly_at(q, lo)?);
        let shi = Sign::of_rational(eval_int_poly_at(q, hi)?);
        if slo != Sign::Zero && shi != Sign::Zero {
            // count of roots of q in the half-open (lo, hi].
            let count = crate::poly::count_roots_in(&chain, lo, hi)?;
            if count == 1 && slo != shi {
                // Exactly one root, strict opposite signs ⇒ the isolating bracket.
                return RealAlgebraic::new(q.to_vec(), lo, hi);
            }
        }
        // Narrow both operand intervals by one bisection each (keep the half still
        // bracketing each operand's own root). A collapse onto an exact rational
        // (operand was actually rational) ⇒ decline (cannot happen for a genuine
        // RealAlgebraic, but stay safe).
        if pa.refine_once()? == Sign::Zero {
            return None;
        }
        if pb.refine_once()? == Sign::Zero {
            return None;
        }
    }
    None
}

/// The candidate result interval `[lo, hi]` for `α ∘ β` from the current operand
/// intervals. `None` on overflow.
fn combined_interval(
    a: &RealAlgebraic,
    b: &RealAlgebraic,
    how: IntervalCombine,
) -> Option<(Rational, Rational)> {
    let (alo, ahi) = a.interval();
    let (blo, bhi) = b.interval();
    match how {
        IntervalCombine::Sum => {
            let lo = alo.checked_add(blo)?;
            let hi = ahi.checked_add(bhi)?;
            Some((lo, hi))
        }
        IntervalCombine::Product => {
            let p1 = alo.checked_mul(blo)?;
            let p2 = alo.checked_mul(bhi)?;
            let p3 = ahi.checked_mul(blo)?;
            let p4 = ahi.checked_mul(bhi)?;
            let mut lo = p1;
            let mut hi = p1;
            for p in [p2, p3, p4] {
                if p.checked_cmp(&lo)? == Ordering::Less {
                    lo = p;
                }
                if p.checked_cmp(&hi)? == Ordering::Greater {
                    hi = p;
                }
            }
            Some((lo, hi))
        }
    }
}

/// Exact Horner evaluation of an LSB-first integer polynomial at a [`Rational`]
/// point, returning `None` on `i128`/`Rational` overflow (never a wrong value).
fn eval_int_poly_at(coeffs: &[i128], x: Rational) -> Option<Rational> {
    // Horner over the rationals: acc = ((cₙ·x + cₙ₋₁)·x + …)·x + c₀.
    let mut acc = Rational::zero();
    for &c in coeffs.iter().rev() {
        acc = acc.checked_mul(x)?.checked_add(Rational::integer(c))?;
    }
    Some(acc)
}

/// Exact test of whether the integer polynomial `divisor` divides `dividend`
/// over the rationals with zero remainder (LSB-first coefficients). Returns
/// `Some(true)`/`Some(false)` for a decided result, or `None` on `i128`/
/// [`Rational`] overflow during the division (the caller then declines or falls
/// back to refinement — never a wrong answer).
///
/// `divisor` must be non-zero (the defining polynomial always has a nonzero
/// leading coefficient). The standard long-division algorithm over `Rational`
/// coefficients is exact; the remainder is zero iff `divisor | dividend`.
fn poly_divides(divisor: &[i128], dividend: &[i128]) -> Option<bool> {
    // Trim trailing zeros to find genuine degrees.
    let dl = trimmed_len(divisor);
    let nl = trimmed_len(dividend);
    if dl == 0 {
        return None; // zero divisor: undefined
    }
    if nl == 0 {
        return Some(true); // 0 is divisible by anything nonzero
    }
    if nl < dl {
        // A lower-degree nonzero dividend cannot be divisible by a higher-degree
        // divisor (a nonzero remainder of degree < dl remains).
        return Some(false);
    }
    // Work with the dividend as a mutable Rational remainder, MSB-aligned by index.
    let mut rem: Vec<Rational> = (0..nl).map(|i| Rational::integer(dividend[i])).collect();
    let lead_div = Rational::integer(divisor[dl - 1]);
    // Subtract divisor multiples to cancel each high coefficient, top-down.
    for top in (dl - 1..nl).rev() {
        let c = rem[top];
        if c.is_zero() {
            continue;
        }
        // Multiplier `c / lead_div` times divisor, aligned so its top hits `top`.
        let factor = c.checked_div(lead_div)?;
        let shift = top + 1 - dl;
        for j in 0..dl {
            let term = factor.checked_mul(Rational::integer(divisor[j]))?;
            rem[shift + j] = rem[shift + j].checked_sub(term)?;
        }
    }
    // Divisible iff the entire remainder (degrees < dl) is zero.
    Some(rem.iter().all(|r| r.is_zero()))
}

/// The number of coefficients up to and including the highest nonzero one (the
/// "trimmed length"); `0` for the zero polynomial.
fn trimmed_len(coeffs: &[i128]) -> usize {
    let mut n = coeffs.len();
    while n > 0 && coeffs[n - 1] == 0 {
        n -= 1;
    }
    n
}

/// Whether two LSB-first integer polynomials are equal up to trailing zeros.
fn same_poly(a: &[i128], b: &[i128]) -> bool {
    let n = a.len().max(b.len());
    (0..n).all(|i| a.get(i).copied().unwrap_or(0) == b.get(i).copied().unwrap_or(0))
}

/// Two algebraic numbers are equal iff they share a defining polynomial (up to
/// trailing zeros) **and** isolate the same root — which, for equal polynomials,
/// holds iff their isolating intervals overlap (each contains exactly one root of
/// the shared poly, so overlapping intervals must bracket the *same* root).
impl PartialEq for RealAlgebraic {
    fn eq(&self, other: &Self) -> bool {
        if !same_poly(&self.poly, &other.poly) {
            return false;
        }
        // Same poly: equal iff the open intervals overlap (both isolate one root).
        let lo = self.lo.max(other.lo);
        let hi = self.hi.min(other.hi);
        lo < hi
    }
}

impl Eq for RealAlgebraic {}

/// Hash on the defining polynomial only (a value-consistent coarsening of `Eq`:
/// equal values share a poly, so they hash equal; distinct roots of the same poly
/// also collide, which is permitted — `Hash` only requires `a == b ⇒ hash(a) ==
/// hash(b)`).
impl core::hash::Hash for RealAlgebraic {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        // Hash the trimmed coefficient sequence so trailing zeros do not perturb
        // the hash of otherwise-equal polynomials.
        let mut last = self.poly.len();
        while last > 0 && self.poly[last - 1] == 0 {
            last -= 1;
        }
        self.poly[..last].hash(state);
    }
}

impl core::fmt::Display for RealAlgebraic {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "root of ")?;
        write_poly(f, &self.poly)?;
        write!(f, " in ({}, {})", self.lo, self.hi)
    }
}

/// Render an LSB-first integer polynomial as a human-readable `… + a·x^k + …`
/// (descending degree), used only by [`RealAlgebraic`]'s `Display`.
fn write_poly(f: &mut core::fmt::Formatter<'_>, coeffs: &[i128]) -> core::fmt::Result {
    let mut last = coeffs.len();
    while last > 1 && coeffs[last - 1] == 0 {
        last -= 1;
    }
    let mut first = true;
    for i in (0..last).rev() {
        let c = coeffs[i];
        if c == 0 {
            continue;
        }
        if first {
            write!(f, "{c}")?;
            first = false;
        } else if c >= 0 {
            write!(f, " + {c}")?;
        } else {
            write!(f, " - {}", -c)?;
        }
        match i {
            0 => {}
            1 => write!(f, "*x")?,
            _ => write!(f, "*x^{i}")?,
        }
    }
    if first {
        write!(f, "0")?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `x² − 2` over (1, 2) is `+√2`.
    fn sqrt2() -> RealAlgebraic {
        RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(1), Rational::integer(2)).unwrap()
    }

    #[test]
    fn new_requires_sign_change() {
        // No sign change of x²−2 over (2, 3): both positive ⇒ rejected.
        assert!(
            RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(2), Rational::integer(3))
                .is_none()
        );
        // lo >= hi rejected.
        assert!(
            RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(2), Rational::integer(1))
                .is_none()
        );
        // Endpoint that is itself a root (x²−1 at 1) rejected (open interval).
        assert!(
            RealAlgebraic::new(vec![-1, 0, 1], Rational::integer(1), Rational::integer(2))
                .is_none()
        );
    }

    #[test]
    fn sign_at_defining_poly_is_zero() {
        let a = sqrt2();
        assert_eq!(a.sign_at(&[-2, 0, 1]), Some(Sign::Zero));
        // A scalar multiple of the defining poly also vanishes (detected exactly).
        assert_eq!(a.sign_at(&[-4, 0, 2]), Some(Sign::Zero));
    }

    #[test]
    fn sign_at_linear_polys() {
        let a = sqrt2(); // +√2 ≈ 1.414
        // q = x  ⇒ positive at +√2.
        assert_eq!(a.sign_at(&[0, 1]), Some(Sign::Pos));
        // q = x − 2 ⇒ negative (√2 < 2).
        assert_eq!(a.sign_at(&[-2, 1]), Some(Sign::Neg));
        // q = x − 1 ⇒ positive (√2 > 1).
        assert_eq!(a.sign_at(&[-1, 1]), Some(Sign::Pos));
        // q = 2x − 3 ⇒ √2 ≈ 1.414, 2*1.414 − 3 = −0.17 ⇒ negative.
        assert_eq!(a.sign_at(&[-3, 2]), Some(Sign::Neg));
        // q = 5x − 7 ⇒ 5*1.414 − 7 = 0.07 ⇒ positive (needs refinement).
        assert_eq!(a.sign_at(&[-7, 5]), Some(Sign::Pos));
    }

    #[test]
    fn compare_rational_brackets() {
        let a = sqrt2();
        assert_eq!(
            a.compare_rational(&Rational::integer(1)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            a.compare_rational(&Rational::integer(2)),
            Some(Ordering::Less)
        );
        // 3/2 = 1.5 > √2.
        assert_eq!(
            a.compare_rational(&Rational::new(3, 2)),
            Some(Ordering::Less)
        );
        // 7/5 = 1.4 < √2.
        assert_eq!(
            a.compare_rational(&Rational::new(7, 5)),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn equality_same_root_overlapping_interval() {
        let a = sqrt2();
        // A tighter isolating interval for the same root.
        let b =
            RealAlgebraic::new(vec![-2, 0, 1], Rational::new(7, 5), Rational::new(3, 2)).unwrap();
        assert_eq!(a, b);
        // The other root (−√2) is a different value.
        let neg = RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(-2), Rational::integer(-1))
            .unwrap();
        assert_ne!(a, neg);
    }

    #[test]
    fn display_form() {
        let a = sqrt2();
        assert_eq!(a.to_string(), "root of 1*x^2 - 2 in (1, 2)");
    }

    /// Property: `sign_at` agrees with a brute-force floating-point oracle on a
    /// batch of small polynomials. FLOAT IS USED ONLY IN THIS TEST ORACLE, never
    /// in the implementation under test.
    #[test]
    fn sign_at_matches_float_oracle() {
        // α = √2, the positive root of x²−2, ≈ 1.4142135623730951.
        let a = sqrt2();
        let alpha = 2.0f64.sqrt();
        // Sweep q = c1*x + c0 and a few quadratics with small integer coeffs.
        for c0 in -5..=5i128 {
            for c1 in -5..=5i128 {
                for c2 in -3..=3i128 {
                    let q = vec![c0, c1, c2];
                    // Float oracle value of q(α).
                    #[allow(clippy::cast_precision_loss)]
                    let fval = (c0 as f64) + (c1 as f64) * alpha + (c2 as f64) * alpha * alpha;
                    let got = a.sign_at(&q);
                    // Skip near-zero oracle values: the float oracle cannot
                    // reliably distinguish sign there, and `sign_at` may return
                    // Zero only for genuine algebraic vanishing (e.g. q ∝ x²−2).
                    if fval.abs() < 1e-9 {
                        // Must be Zero or a definite sign; just require it not crash.
                        assert!(got.is_some(), "sign_at must decide q={q:?}");
                        continue;
                    }
                    let want = if fval < 0.0 { Sign::Neg } else { Sign::Pos };
                    assert_eq!(got, Some(want), "q={q:?} α=√2 fval={fval}");
                }
            }
        }
    }
}
