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
