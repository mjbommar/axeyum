//! Exact interval arithmetic over rationals — rigorous enclosures.
//!
//! An [`Interval`] is a closed interval `[lower, upper]` of exact [`Rational`]
//! endpoints with `lower ≤ upper`. It is the numerics analogue of the rest of
//! this crate: where floating-point interval arithmetic rounds endpoints
//! outward to stay sound, here the endpoints are *exact* rationals, so every
//! operation returns the tightest rational interval that still **encloses the
//! true set of possible values**. The enclosure property is the certificate —
//! `f([a, b])` always contains `{ f(x) : x ∈ [a, b] }`, checked in the tests by
//! sampling concrete points and confirming membership.
//!
//! All arithmetic is bounded to the `i128` range of `Rational` (ADR-0014/0015):
//! operations that would overflow return `None` rather than a wrapped (unsound)
//! result, so a graceful failure never masquerades as a valid enclosure.

use axeyum_ir::Rational;
use core::cmp::Ordering;

/// A closed interval `[lower, upper]` of exact rationals with `lower ≤ upper`.
///
/// Every value is a valid enclosure by construction: constructors reject
/// `lower > upper`, and each operation preserves the invariant while returning
/// an interval that contains the true image of the underlying operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    /// The lower endpoint (inclusive); always `≤ upper`.
    lower: Rational,
    /// The upper endpoint (inclusive); always `≥ lower`.
    upper: Rational,
}

impl Interval {
    /// The interval `[a, b]`, or `None` if `a > b` (an empty/invalid interval)
    /// or if the endpoint comparison overflows.
    #[must_use]
    pub fn new(a: Rational, b: Rational) -> Option<Interval> {
        match a.checked_cmp(&b)? {
            Ordering::Greater => None,
            _ => Some(Interval { lower: a, upper: b }),
        }
    }

    /// The degenerate (point) interval `[a, a]`.
    #[must_use]
    pub fn degenerate(a: Rational) -> Interval {
        Interval { lower: a, upper: a }
    }

    /// The lower endpoint.
    #[must_use]
    pub fn lower(&self) -> Rational {
        self.lower
    }

    /// The upper endpoint.
    #[must_use]
    pub fn upper(&self) -> Rational {
        self.upper
    }

    /// The width `upper − lower` (always `≥ 0`).
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow while subtracting the endpoints.
    #[must_use]
    pub fn width(&self) -> Rational {
        self.upper
            .checked_sub(self.lower)
            .expect("interval width overflow")
    }

    /// The midpoint `(lower + upper) / 2`.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow while summing or halving the endpoints.
    #[must_use]
    pub fn midpoint(&self) -> Rational {
        self.lower
            .checked_add(self.upper)
            .expect("interval midpoint sum overflow")
            .checked_div(Rational::integer(2))
            .expect("interval midpoint halving overflow")
    }

    /// Returns `true` if `x` lies in `[lower, upper]`.
    #[must_use]
    pub fn contains(&self, x: Rational) -> bool {
        self.lower <= x && x <= self.upper
    }

    /// Returns `true` if `other` is entirely contained in `self`.
    #[must_use]
    pub fn contains_interval(&self, other: &Interval) -> bool {
        self.lower <= other.lower && other.upper <= self.upper
    }

    /// The interval sum `self + other = [l₁+l₂, u₁+u₂]`, or `None` on overflow.
    #[must_use]
    pub fn add(&self, other: &Interval) -> Option<Interval> {
        let lower = self.lower.checked_add(other.lower)?;
        let upper = self.upper.checked_add(other.upper)?;
        Interval::new(lower, upper)
    }

    /// The interval difference `self − other = [l₁−u₂, u₁−l₂]`, or `None` on
    /// overflow.
    #[must_use]
    pub fn sub(&self, other: &Interval) -> Option<Interval> {
        let lower = self.lower.checked_sub(other.upper)?;
        let upper = self.upper.checked_sub(other.lower)?;
        Interval::new(lower, upper)
    }

    /// The interval product `self · other`, or `None` on overflow.
    ///
    /// Uses the four-product rule: the product interval spans the minimum and
    /// maximum of the four endpoint products, which is exactly the image of
    /// `{ x·y : x ∈ self, y ∈ other }` because the product is monotone in each
    /// argument.
    #[must_use]
    pub fn mul(&self, other: &Interval) -> Option<Interval> {
        let p1 = self.lower.checked_mul(other.lower)?;
        let p2 = self.lower.checked_mul(other.upper)?;
        let p3 = self.upper.checked_mul(other.lower)?;
        let p4 = self.upper.checked_mul(other.upper)?;
        let lower = rat_min(rat_min(p1, p2)?, rat_min(p3, p4)?)?;
        let upper = rat_max(rat_max(p1, p2)?, rat_max(p3, p4)?)?;
        Interval::new(lower, upper)
    }

    /// The negation `−self = [−upper, −lower]`, or `None` on overflow.
    #[must_use]
    pub fn neg(&self) -> Option<Interval> {
        let lower = self.upper.checked_neg()?;
        let upper = self.lower.checked_neg()?;
        Interval::new(lower, upper)
    }

    /// The interval quotient `self / other`, or `None` if `other` contains `0`
    /// (division by a set including zero is unbounded) or on overflow.
    #[must_use]
    pub fn div(&self, other: &Interval) -> Option<Interval> {
        if other.contains(Rational::zero()) {
            return None;
        }
        // `other` is bounded away from zero, so both endpoints share a sign and
        // `1/other = [1/upper, 1/lower]` is a valid interval; multiply by it.
        let one = Rational::integer(1);
        let recip_lower = one.checked_div(other.upper)?;
        let recip_upper = one.checked_div(other.lower)?;
        let recip = Interval::new(recip_lower, recip_upper)?;
        self.mul(&recip)
    }

    /// The `n`-th power `selfⁿ`, or `None` on overflow.
    ///
    /// For even `n` on an interval straddling `0` the minimum of the image is
    /// `0` (not an endpoint power), so this case is handled specially; `pow(0)`
    /// is the point interval `[1, 1]`.
    #[must_use]
    pub fn pow(&self, n: u32) -> Option<Interval> {
        if n == 0 {
            return Some(Interval::degenerate(Rational::integer(1)));
        }
        let lower_pow = rat_pow(self.lower, n)?;
        let upper_pow = rat_pow(self.upper, n)?;
        let zero = Rational::zero();
        let straddles_zero = self.lower <= zero && zero <= self.upper;
        if n.is_multiple_of(2) && straddles_zero {
            // Even power of an interval containing 0: minimum is 0, maximum is
            // the larger endpoint power.
            let upper = rat_max(lower_pow, upper_pow)?;
            Interval::new(zero, upper)
        } else {
            // Odd power (monotone), or even power away from 0 (both endpoints
            // same sign): the image is bounded by the endpoint powers.
            let lower = rat_min(lower_pow, upper_pow)?;
            let upper = rat_max(lower_pow, upper_pow)?;
            Interval::new(lower, upper)
        }
    }

    /// The intersection `self ∩ other`, or `None` if the intervals are disjoint
    /// (or the comparison overflows).
    #[must_use]
    pub fn intersection(&self, other: &Interval) -> Option<Interval> {
        let lower = rat_max(self.lower, other.lower)?;
        let upper = rat_min(self.upper, other.upper)?;
        // `new` returns `None` exactly when `lower > upper`, i.e. disjoint.
        Interval::new(lower, upper)
    }

    /// The convex hull `self ∪ other` — the smallest interval enclosing both,
    /// or `None` on overflow.
    #[must_use]
    pub fn hull(&self, other: &Interval) -> Option<Interval> {
        let lower = rat_min(self.lower, other.lower)?;
        let upper = rat_max(self.upper, other.upper)?;
        Interval::new(lower, upper)
    }

    /// The absolute-value interval `{ |x| : x ∈ self }`.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow while negating an endpoint (only reachable when
    /// an endpoint numerator is `i128::MIN`).
    #[must_use]
    pub fn abs(&self) -> Interval {
        let zero = Rational::zero();
        if self.lower >= zero {
            // Wholly non-negative: unchanged.
            *self
        } else if self.upper <= zero {
            // Wholly non-positive: negate and swap endpoints.
            let lower = self.upper.checked_neg().expect("interval abs overflow");
            let upper = self.lower.checked_neg().expect("interval abs overflow");
            Interval { lower, upper }
        } else {
            // Straddles zero: minimum is 0, maximum is the larger magnitude.
            let neg_lower = self.lower.checked_neg().expect("interval abs overflow");
            let upper = rat_max(neg_lower, self.upper).expect("interval abs overflow");
            Interval { lower: zero, upper }
        }
    }
}

/// Evaluates the polynomial with LSB-first coefficients `coeffs` (so `coeffs[0]`
/// is the constant term and `coeffs[k]` the coefficient of `xᵏ`) over the
/// interval `x`, returning a rigorous enclosure of its image, or `None` on
/// overflow.
///
/// The evaluation is Horner's scheme lifted into interval arithmetic. The result
/// is guaranteed to contain `{ p(t) : t ∈ x }`, though (as always with interval
/// Horner) it may be wider than the exact image because each `x` occurrence is
/// treated independently. An empty `coeffs` denotes the zero polynomial and
/// yields the point interval `[0, 0]`.
#[must_use]
pub fn evaluate_polynomial(coeffs: &[Rational], x: &Interval) -> Option<Interval> {
    // Horner from the highest-degree coefficient downwards.
    let mut iter = coeffs.iter().rev();
    let leading = iter.next().copied().unwrap_or_else(Rational::zero);
    let mut acc = Interval::degenerate(leading);
    for &coeff in iter {
        acc = acc.mul(x)?.add(&Interval::degenerate(coeff))?;
    }
    Some(acc)
}

/// The lesser of two rationals, or `None` if the comparison overflows.
fn rat_min(a: Rational, b: Rational) -> Option<Rational> {
    match a.checked_cmp(&b)? {
        Ordering::Greater => Some(b),
        _ => Some(a),
    }
}

/// The greater of two rationals, or `None` if the comparison overflows.
fn rat_max(a: Rational, b: Rational) -> Option<Rational> {
    match a.checked_cmp(&b)? {
        Ordering::Less => Some(b),
        _ => Some(a),
    }
}

/// The `n`-th power of a rational by repeated exact multiplication, or `None`
/// on overflow. `n == 0` yields `1`.
fn rat_pow(base: Rational, n: u32) -> Option<Rational> {
    let mut result = Rational::integer(1);
    for _ in 0..n {
        result = result.checked_mul(base)?;
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::{Interval, evaluate_polynomial};
    use axeyum_ir::Rational;

    /// Builds `[a, b]` from integers, asserting it is a valid interval.
    fn ivl(a: i128, b: i128) -> Interval {
        Interval::new(Rational::integer(a), Rational::integer(b)).expect("valid interval")
    }

    #[test]
    fn addition_shifts_both_endpoints() {
        // [1,2] + [3,4] = [4,6].
        assert_eq!(ivl(1, 2).add(&ivl(3, 4)), Some(ivl(4, 6)));
    }

    #[test]
    fn subtraction_crosses_endpoints() {
        // [1,2] − [3,4] = [1−4, 2−3] = [−3,−1].
        assert_eq!(ivl(1, 2).sub(&ivl(3, 4)), Some(ivl(-3, -1)));
    }

    #[test]
    fn multiplication_uses_four_products() {
        // [−1,2] · [3,4]: products −4,−3,6,8 ⇒ [−4,8].
        assert_eq!(ivl(-1, 2).mul(&ivl(3, 4)), Some(ivl(-4, 8)));
    }

    #[test]
    fn negation_reflects_and_swaps() {
        // −[−1,2] = [−2,1].
        assert_eq!(ivl(-1, 2).neg(), Some(ivl(-2, 1)));
    }

    #[test]
    fn division_by_positive_interval() {
        // [1,2] / [2,4] = [1/4, 1].
        let quotient = ivl(1, 2).div(&ivl(2, 4)).expect("divisor avoids zero");
        let expected = Interval::new(Rational::new(1, 4), Rational::integer(1)).expect("valid");
        assert_eq!(quotient, expected);
    }

    #[test]
    fn division_by_interval_containing_zero_is_none() {
        // Divisor [−1,2] contains 0 ⇒ unbounded ⇒ None.
        assert_eq!(ivl(1, 2).div(&ivl(-1, 2)), None);
        // A divisor touching zero at an endpoint is also rejected.
        assert_eq!(ivl(1, 2).div(&ivl(0, 4)), None);
    }

    #[test]
    fn even_power_straddling_zero_has_zero_minimum() {
        // [−2,3]² = [0,9] because the interval crosses 0.
        assert_eq!(ivl(-2, 3).pow(2), Some(ivl(0, 9)));
    }

    #[test]
    fn even_power_away_from_zero_keeps_endpoint_minimum() {
        // [1,3]² = [1,9].
        assert_eq!(ivl(1, 3).pow(2), Some(ivl(1, 9)));
    }

    #[test]
    fn odd_power_is_monotone() {
        // [−2,3]³ = [−8,27].
        assert_eq!(ivl(-2, 3).pow(3), Some(ivl(-8, 27)));
        // The zeroth power is the point interval [1,1].
        assert_eq!(ivl(-2, 3).pow(0), Some(ivl(1, 1)));
    }

    #[test]
    fn intersection_of_overlapping_intervals() {
        // [0,2] ∩ [1,3] = [1,2].
        assert_eq!(ivl(0, 2).intersection(&ivl(1, 3)), Some(ivl(1, 2)));
    }

    #[test]
    fn intersection_of_disjoint_intervals_is_none() {
        // [0,1] ∩ [3,4] = ∅ ⇒ None.
        assert_eq!(ivl(0, 1).intersection(&ivl(3, 4)), None);
    }

    #[test]
    fn hull_spans_both_intervals() {
        // hull([0,1], [3,4]) = [0,4].
        assert_eq!(ivl(0, 1).hull(&ivl(3, 4)), Some(ivl(0, 4)));
    }

    #[test]
    fn abs_handles_sign_and_straddle() {
        assert_eq!(ivl(1, 3).abs(), ivl(1, 3)); // non-negative
        assert_eq!(ivl(-4, -1).abs(), ivl(1, 4)); // non-positive: reflect+swap
        assert_eq!(ivl(-2, 3).abs(), ivl(0, 3)); // straddles: min is 0
    }

    #[test]
    fn width_and_midpoint_are_exact() {
        let interval = ivl(1, 4);
        assert_eq!(interval.width(), Rational::integer(3));
        assert_eq!(interval.midpoint(), Rational::new(5, 2));
        assert_eq!(
            Interval::degenerate(Rational::integer(7)).width(),
            Rational::zero()
        );
    }

    #[test]
    fn membership_checks() {
        let interval = ivl(1, 3);
        assert!(interval.contains(Rational::integer(1))); // lower boundary
        assert!(interval.contains(Rational::new(5, 2))); // interior
        assert!(interval.contains(Rational::integer(3))); // upper boundary
        assert!(!interval.contains(Rational::integer(4))); // outside
        assert!(interval.contains_interval(&ivl(1, 2)));
        assert!(!interval.contains_interval(&ivl(0, 2)));
    }

    #[test]
    fn evaluate_polynomial_encloses_x_squared_minus_two() {
        // p(x) = x² − 2 with LSB-first coefficients [−2, 0, 1] over [1,2].
        // x² ∈ [1,4], so p ∈ [−1,2].
        let coeffs = [
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let x = ivl(1, 2);
        let enclosure = evaluate_polynomial(&coeffs, &x).expect("no overflow");
        let expected = Interval::new(Rational::integer(-1), Rational::integer(2)).expect("valid");
        assert_eq!(enclosure, expected);
    }

    #[test]
    fn evaluate_polynomial_enclosure_is_sound() {
        // Sample points of p(x) = x² − 2 across [1,2] must lie in the enclosure,
        // confirming the enclosure property (the soundness certificate).
        let coeffs = [
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let x = ivl(1, 2);
        let enclosure = evaluate_polynomial(&coeffs, &x).expect("no overflow");
        for numer in 4..=8 {
            // t = numer/4 ranges over 1, 5/4, 6/4, 7/4, 2.
            let t = Rational::new(numer, 4);
            // p(t) = t² − 2.
            let value = t
                .checked_mul(t)
                .and_then(|sq| sq.checked_sub(Rational::integer(2)))
                .expect("no overflow");
            assert!(
                enclosure.contains(value),
                "p({t}) = {value} escaped the enclosure {enclosure:?}",
            );
        }
    }

    #[test]
    fn empty_polynomial_is_zero() {
        // No coefficients ⇒ the zero polynomial ⇒ [0,0] regardless of x.
        let enclosure = evaluate_polynomial(&[], &ivl(1, 5)).expect("no overflow");
        assert_eq!(enclosure, Interval::degenerate(Rational::zero()));
    }
}
