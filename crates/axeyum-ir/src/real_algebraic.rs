//! Real algebraic numbers as a defining polynomial plus an isolating interval
//! (ADR-0038; arbitrary-precision storage per ADR-0045).
//!
//! A [`RealAlgebraic`] is an *exact*, irrational-capable real value: an integer
//! polynomial `poly` (LSB-first, mirroring the NRA/NIA `Poly` layout) together
//! with a rational open interval `(lo, hi)` that contains **exactly one** real
//! root of `poly`. That unique root *is* the value. The single-root invariant is
//! established by construction (a sign change of `poly` between the endpoints,
//! the interval already isolated from any other root by the decider's root
//! isolation).
//!
//! **Storage (ADR-0045):** the defining polynomial is `Vec<BigInt>` and the
//! interval endpoints are [`num_rational::BigRational`] — arbitrary precision.
//! This removes the former `i128`-storage ceiling: algebraic field arithmetic
//! (`add`/`mul`/`neg`) computes entirely in bignum (via the `crate::poly_big`
//! primitives), so higher-degree coupled NRA witnesses (e.g. the degree-4
//! nested-radical coordinates of `x²+y²=4 ∧ x·y=1`) now decide instead of
//! declining on an intermediate-or-final overflow. Algebraic values appear only in
//! NRA witnesses (rare), so the always-bignum storage is fine; the core
//! [`Rational`] type (used everywhere) stays `i128`.
//!
//! The operations the single-variable NRA decider needs to build and
//! **replay-check** an irrational witness:
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
//! - algebraic field arithmetic ([`RealAlgebraic::neg`], [`RealAlgebraic::add`],
//!   [`RealAlgebraic::mul`]) — the exact `−α`, `α + β`, `α · β` via the
//!   resultant + squarefree + Sturm-isolation primitives in `crate::poly_big`,
//!   computed in arbitrary precision.
//!
//! **No floating point anywhere.** Every sign test is exact over `BigInt` /
//! [`BigRational`]. Refinement is bounded; a failure to converge within the bound
//! returns `None`, and the caller declines (a sound `unknown`) rather than risk a
//! wrong answer. The resultant/Sturm work is bounded by degree/dimension caps in
//! `crate::poly_big` → graceful decline, never OOM/hang.

use core::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use crate::poly_big::{
    BigAlgebraic, Combine, big_eval_int_at, big_poly_divides, big_sign, bigint_poly_from_i128,
    bigrational_from_i128, combine_retry,
};
use crate::rational::Rational;

/// The maximum number of bisection steps [`RealAlgebraic::sign_at`] and
/// [`RealAlgebraic::compare_rational`] will take before giving up (returning
/// `None` → the caller declines). Each step halves the interval, so the
/// resolution after `N` steps is `(hi − lo) / 2^N`; 256 steps is far more than
/// enough to separate any root the decider produces from a distinct sign of a
/// bounded polynomial, while staying cheap.
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

/// A real algebraic number: the unique real root of `poly` lying in the open
/// interval `(lo, hi)`.
///
/// Invariant (established by [`RealAlgebraic::new`] / [`RealAlgebraic::new_big`]):
/// `poly` has *exactly one* real root in `(lo, hi)`, witnessed by
/// `sign(poly(lo)) ≠ sign(poly(hi))` (both nonzero), and the interval is otherwise
/// root-isolated by the caller. The value denoted is that root.
#[derive(Debug, Clone)]
pub struct RealAlgebraic {
    /// The arbitrary-precision data is held behind a single [`Box`] so the
    /// [`RealAlgebraic`] (and hence [`crate::Value`]) stays a one-pointer-wide,
    /// cheaply-`Clone`/`Copy`-adjacent handle: the bignum polynomial and interval
    /// are large, and inlining them would bloat every `Value`-carrying enum (and
    /// trip `result_large_err`). Algebraic values are rare (NRA witnesses only), so
    /// the extra indirection is irrelevant.
    inner: Box<Repr>,
}

/// The heap-allocated payload of a [`RealAlgebraic`].
#[derive(Debug, Clone)]
struct Repr {
    /// The defining integer polynomial, LSB-first (`coeffs[i]` is the coefficient
    /// of `xⁱ`), in arbitrary precision. Trailing zeros are not required to be
    /// trimmed, but the leading coefficient must be nonzero for the degree to be
    /// meaningful.
    poly: Vec<BigInt>,
    /// The lower endpoint of the isolating interval (exclusive).
    lo: BigRational,
    /// The upper endpoint of the isolating interval (exclusive).
    hi: BigRational,
}

/// The sign of a [`BigRational`] as a [`Sign`].
fn sign_of_big(r: &BigRational) -> Sign {
    big_sign(r)
}

impl RealAlgebraic {
    /// Builds a real algebraic number from an `i128` defining polynomial and an
    /// `i128`-[`Rational`] isolating interval `(lo, hi)`, lifting both to arbitrary
    /// precision. This convenience constructor keeps the `i128`-producing root
    /// isolation in the solver unchanged. Returns `None` if the one-root invariant
    /// cannot be confirmed (see [`RealAlgebraic::new_big`]).
    #[must_use]
    pub fn new(poly: Vec<i128>, lo: Rational, hi: Rational) -> Option<RealAlgebraic> {
        let poly = poly.into_iter().map(BigInt::from).collect();
        let lo = bigrational_from_i128(lo.numerator(), lo.denominator());
        let hi = bigrational_from_i128(hi.numerator(), hi.denominator());
        RealAlgebraic::new_big(poly, lo, hi)
    }

    /// Builds a real algebraic number from a bignum defining polynomial and an
    /// arbitrary-precision isolating interval `(lo, hi)`, returning `None` if the
    /// one-root invariant cannot be confirmed: `lo < hi`, and the polynomial must
    /// take a *strictly opposite, nonzero* sign at the two endpoints (a sign change
    /// ⇒ at least one root; the caller guarantees isolation ⇒ exactly one).
    ///
    /// The endpoint sign-change check is exact (Horner over [`BigRational`]). If
    /// `poly(lo)` or `poly(hi)` is zero, the endpoint *is* the root — but the
    /// interval is open, so the caller should instead represent that exact rational
    /// root as `Value::Real`; here we reject it (`None`).
    #[must_use]
    pub fn new_big(poly: Vec<BigInt>, lo: BigRational, hi: BigRational) -> Option<RealAlgebraic> {
        if lo >= hi {
            return None;
        }
        let slo = sign_of_big(&big_eval_int_at(&poly, &lo));
        let shi = sign_of_big(&big_eval_int_at(&poly, &hi));
        // Strict opposite, nonzero signs ⇒ a root strictly inside (lo, hi).
        match (slo, shi) {
            (Sign::Neg, Sign::Pos) | (Sign::Pos, Sign::Neg) => Some(RealAlgebraic {
                inner: Box::new(Repr { poly, lo, hi }),
            }),
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
        let poly = vec![BigInt::from(-p), BigInt::from(q)];
        // The bracket (c − 1, c + 1), built directly in bignum.
        let c_big = bigrational_from_i128(p, q);
        let one = BigRational::from(BigInt::from(1));
        let lo = &c_big - &one;
        let hi = &c_big + &one;
        RealAlgebraic::new_big(poly, lo, hi)
    }

    /// The defining polynomial (LSB-first bignum-integer coefficients).
    #[must_use]
    pub fn defining_poly(&self) -> &[BigInt] {
        &self.inner.poly
    }

    /// The defining polynomial as `i128` coefficients, or `None` if any coefficient
    /// does not fit `i128`. Used by the solver's `i128`-backed NRA post-processing
    /// (rationalization, affine maps, coarsening): on `None` those paths decline
    /// soundly (a sound `Unknown`), never a wrong verdict.
    #[must_use]
    pub fn defining_poly_i128(&self) -> Option<Vec<i128>> {
        let mut out = Vec::with_capacity(self.inner.poly.len());
        for c in &self.inner.poly {
            out.push(i128::try_from(c.clone()).ok()?);
        }
        Some(out)
    }

    /// The current isolating interval `(lo, hi)` as `i128` [`Rational`]s, or `None`
    /// if either endpoint does not fit `i128`.
    #[must_use]
    pub fn interval(&self) -> Option<(Rational, Rational)> {
        Some((
            bigrational_to_rational(&self.inner.lo)?,
            bigrational_to_rational(&self.inner.hi)?,
        ))
    }

    /// The current isolating interval `(lo, hi)` in arbitrary precision.
    #[must_use]
    pub fn interval_big(&self) -> (BigRational, BigRational) {
        (self.inner.lo.clone(), self.inner.hi.clone())
    }

    /// Refine the isolating interval *in place* by one bisection step: evaluate
    /// the defining polynomial at the midpoint and keep the half whose endpoints
    /// still straddle the root. Returns `Sign::Zero` if the midpoint *is* the root
    /// (then the value is exactly rational and both endpoints collapse to it), or
    /// the midpoint sign for a successful narrowing.
    fn refine_once(&mut self) -> Sign {
        let two = BigRational::from(BigInt::from(2));
        let mid = (&self.inner.lo + &self.inner.hi) / two;
        let smid = sign_of_big(&big_eval_int_at(&self.inner.poly, &mid));
        if smid == Sign::Zero {
            self.inner.lo = mid.clone();
            self.inner.hi = mid;
            return Sign::Zero;
        }
        let slo = sign_of_big(&big_eval_int_at(&self.inner.poly, &self.inner.lo));
        if slo == smid {
            self.inner.lo = mid;
        } else {
            self.inner.hi = mid;
        }
        smid
    }

    /// The exact [`Sign`] of an arbitrary integer polynomial `q` (given as `i128`
    /// coefficients) evaluated at this algebraic number `α`.
    ///
    /// Strategy (exact, no float): if the defining polynomial divides `q` exactly
    /// over the rationals, then `q(α) = 0` (every root of `poly`, in particular α,
    /// is a root of `q`). This is the only sound way to report `Zero` for an
    /// irrational α. Otherwise refine the isolating interval until `q`'s sign is
    /// constant and nonzero across the bracket, or the interval collapses onto an
    /// exact rational root where `q` can be evaluated directly.
    ///
    /// Returns `None` (→ the caller declines, a sound `unknown`) if a constant
    /// nonzero sign is not reached within `MAX_REFINE_STEPS`.
    #[must_use]
    pub fn sign_at(&self, q: &[i128]) -> Option<Sign> {
        let qbig = bigint_poly_from_i128(q);
        self.sign_at_big(&qbig)
    }

    /// As [`RealAlgebraic::sign_at`] but for a bignum-integer polynomial `q`.
    #[must_use]
    pub fn sign_at_big(&self, q: &[BigInt]) -> Option<Sign> {
        // Exact vanishing test: `poly | q` over the rationals ⇒ q(α) = 0.
        if big_poly_divides(&self.inner.poly, q) {
            return Some(Sign::Zero);
        }
        let mut probe = self.clone();
        for _ in 0..MAX_REFINE_STEPS {
            let vlo = big_eval_int_at(q, &probe.inner.lo);
            let vhi = big_eval_int_at(q, &probe.inner.hi);
            if probe.inner.lo == probe.inner.hi {
                return Some(sign_of_big(&vlo));
            }
            let slo = sign_of_big(&vlo);
            let shi = sign_of_big(&vhi);
            if slo == shi && slo != Sign::Zero {
                return Some(slo);
            }
            if probe.refine_once() == Sign::Zero {
                // Interval collapsed onto an exact rational root r of poly: α = r.
                let qr = big_eval_int_at(q, &probe.inner.lo);
                return Some(sign_of_big(&qr));
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
    /// Returns `None` (→ decline) on non-convergence within `MAX_REFINE_STEPS`.
    #[must_use]
    pub fn compare_rational(&self, c: &Rational) -> Option<Ordering> {
        let c_big = bigrational_from_i128(c.numerator(), c.denominator());
        self.compare_big(&c_big)
    }

    /// As [`RealAlgebraic::compare_rational`] but against a [`BigRational`].
    #[must_use]
    pub fn compare_big(&self, c: &BigRational) -> Option<Ordering> {
        // If `c` is a root of the defining poly inside the (open) bracket, it is α.
        if *c > self.inner.lo
            && *c < self.inner.hi
            && sign_of_big(&big_eval_int_at(&self.inner.poly, c)) == Sign::Zero
        {
            return Some(Ordering::Equal);
        }
        let mut probe = self.clone();
        for _ in 0..MAX_REFINE_STEPS {
            if *c <= probe.inner.lo {
                return Some(Ordering::Greater);
            }
            if *c >= probe.inner.hi {
                return Some(Ordering::Less);
            }
            if probe.refine_once() == Sign::Zero {
                return Some(probe.inner.lo.cmp(c));
            }
        }
        None
    }

    /// A rational strictly inside the current isolating interval — the interval
    /// midpoint — usable as a coarse numeric stand-in (never used for any sign
    /// decision, only for display/diagnostics). `None` if it does not fit `i128`.
    #[must_use]
    pub fn approx_midpoint(&self) -> Option<Rational> {
        let two = BigRational::from(BigInt::from(2));
        let mid = (&self.inner.lo + &self.inner.hi) / two;
        bigrational_to_rational(&mid)
    }

    // ========================================================================
    // Algebraic field arithmetic (ADR-0038, slice 3; ADR-0045 storage): −α,
    // α+β, α·β — now computed entirely in arbitrary precision via
    // `crate::poly_big`. The former i128-fast-path / bignum-retry SPLIT collapses
    // into a single bignum computation: there is no overflow decline on the
    // algebraic arithmetic path, so the headline nested-radical combinations
    // decide. Each returns `Option<RealAlgebraic>`, declining (`None`) only on a
    // degree/dimension/round-cap trip in `poly_big` (graceful decline, never a
    // wrong value). The single-root invariant of the result is re-established by an
    // EXACT Sturm count == 1 with strict opposite-sign endpoints (inside
    // `combine_retry`), exactly as `RealAlgebraic::new_big` requires.
    // ========================================================================

    /// The exact additive inverse `−α`.
    ///
    /// If `α` is the unique root of `p(x)` in `(lo, hi)`, then `−α` is the unique
    /// root of `p(−x)` in `(−hi, −lo)`. `p(−x)` flips the sign of every odd-degree
    /// coefficient. Exact (bignum never overflows).
    #[must_use]
    pub fn neg(&self) -> Option<RealAlgebraic> {
        let mut poly = Vec::with_capacity(self.inner.poly.len());
        for (i, c) in self.inner.poly.iter().enumerate() {
            if i % 2 == 1 {
                poly.push(-c.clone());
            } else {
                poly.push(c.clone());
            }
        }
        let lo = -self.inner.hi.clone();
        let hi = -self.inner.lo.clone();
        RealAlgebraic::new_big(poly, lo, hi)
    }

    /// The exact sum `α + β`, computed in arbitrary precision (no float). `α + β`
    /// is the unique root of the squarefree part of `Res_y(p_α(y), p_β(x − y))`
    /// inside the sum of the operand intervals, isolated by an exact Sturm count.
    /// `None` on a degree/dimension/round-cap trip.
    #[must_use]
    pub fn add(&self, other: &RealAlgebraic) -> Option<RealAlgebraic> {
        self.combine(other, Combine::Sum)
    }

    /// The exact product `α · β`, computed in arbitrary precision (no float). A
    /// [`RealAlgebraic`] is irrational by construction (never the rational `0`), so
    /// `α · β` is the unique root of the squarefree part of the homogenized
    /// resultant `Res_y(p_α(y), y^{deg β}·p_β(x / y))` inside the product of the
    /// operand intervals. `None` on a degree/dimension/round-cap trip.
    #[must_use]
    pub fn mul(&self, other: &RealAlgebraic) -> Option<RealAlgebraic> {
        self.combine(other, Combine::Product)
    }

    /// Shared driver for `add`/`mul`: run the bignum resultant → squarefree →
    /// Sturm-isolation, then wrap the result as a `RealAlgebraic`.
    fn combine(&self, other: &RealAlgebraic, how: Combine) -> Option<RealAlgebraic> {
        let BigAlgebraic { poly, lo, hi } = combine_retry(
            &self.inner.poly,
            &self.inner.lo,
            &self.inner.hi,
            &other.inner.poly,
            &other.inner.lo,
            &other.inner.hi,
            how,
        )?;
        // Re-establish the single-root invariant on the returned interval
        // (defense-in-depth: `combine_retry` already confirmed exactly one root
        // with opposite endpoint signs).
        RealAlgebraic::new_big(poly, lo, hi)
    }
}

/// `BigRational` → `i128` [`Rational`], `None` if numerator or denominator is out
/// of `i128` range. The bignum rational is already in lowest terms.
fn bigrational_to_rational(r: &BigRational) -> Option<Rational> {
    let num = i128::try_from(r.numer().clone()).ok()?;
    let den = i128::try_from(r.denom().clone()).ok()?;
    Rational::checked_new(num, den)
}

/// The number of coefficients up to and including the highest nonzero one (the
/// "trimmed length"); `0` for the zero polynomial.
fn trimmed_len(coeffs: &[BigInt]) -> usize {
    let mut n = coeffs.len();
    while n > 0 && coeffs[n - 1].is_zero() {
        n -= 1;
    }
    n
}

/// Whether two LSB-first bignum-integer polynomials are equal up to trailing
/// zeros.
fn same_poly(a: &[BigInt], b: &[BigInt]) -> bool {
    let n = a.len().max(b.len());
    let zero = BigInt::from(0);
    (0..n).all(|i| a.get(i).unwrap_or(&zero) == b.get(i).unwrap_or(&zero))
}

/// Two algebraic numbers are equal iff they share a defining polynomial (up to
/// trailing zeros) **and** isolate the same root — which, for equal polynomials,
/// holds iff their isolating intervals overlap (each contains exactly one root of
/// the shared poly, so overlapping intervals must bracket the *same* root).
impl PartialEq for RealAlgebraic {
    fn eq(&self, other: &Self) -> bool {
        if !same_poly(&self.inner.poly, &other.inner.poly) {
            return false;
        }
        // Same poly: equal iff the open intervals overlap (both isolate one root).
        let lo = self.inner.lo.clone().max(other.inner.lo.clone());
        let hi = self.inner.hi.clone().min(other.inner.hi.clone());
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
        let n = trimmed_len(&self.inner.poly);
        self.inner.poly[..n].hash(state);
    }
}

impl core::fmt::Display for RealAlgebraic {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "root of ")?;
        write_poly(f, &self.inner.poly)?;
        write!(
            f,
            " in ({}, {})",
            fmt_big(&self.inner.lo),
            fmt_big(&self.inner.hi)
        )
    }
}

/// Render a [`BigRational`] as `n` (integer) or `n/d`.
fn fmt_big(r: &BigRational) -> String {
    use num_traits::One;
    if r.denom().is_one() {
        r.numer().to_string()
    } else {
        format!("{}/{}", r.numer(), r.denom())
    }
}

/// Render an LSB-first bignum-integer polynomial as a human-readable
/// `… + a·x^k + …` (descending degree), used only by [`RealAlgebraic`]'s
/// `Display`.
fn write_poly(f: &mut core::fmt::Formatter<'_>, coeffs: &[BigInt]) -> core::fmt::Result {
    let mut last = coeffs.len();
    while last > 1 && coeffs[last - 1].is_zero() {
        last -= 1;
    }
    let mut first = true;
    for i in (0..last).rev() {
        let c = &coeffs[i];
        if c.is_zero() {
            continue;
        }
        let neg = c.sign() == num_bigint::Sign::Minus;
        if first {
            write!(f, "{c}")?;
            first = false;
        } else if neg {
            write!(f, " - {}", -c)?;
        } else {
            write!(f, " + {c}")?;
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
