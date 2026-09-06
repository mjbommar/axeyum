//! `axeyum_arith::AlgebraicNumber` for this crate's two real-algebraic
//! carriers.
//!
//! ADR-1710's design note (§5) argues that the **trait** for a real algebraic
//! number belongs in `axeyum-arith` while the two concrete carriers stay where
//! they are: [`RealAlgebraic`] is a variant of [`crate::Value`], so moving the
//! struct is a public IR change — the churn ADR-1702 declined for `Rational`.
//! This module is that decision made real. Both carriers gain one interface
//! `axeyum-cas` can program against, and neither moves.
//!
//! # The three operations, and why each is exact
//!
//! Both carriers are the same triple: an integer defining polynomial `p`
//! (least-significant-first) and an isolating interval `(lo, hi)` with
//! **exactly one** root of `p` inside and neither endpoint a root.
//!
//! - **`sign`** needs no refinement at all. If `lo ≥ 0` the root exceeds `lo`
//!   and is positive; if `hi ≤ 0` it is negative. Otherwise `0` lies strictly
//!   inside, so the root is zero exactly when `p(0) = 0` — the constant
//!   coefficient — and when it is not, the root lies in `(lo, 0)` precisely
//!   when `p` changes sign there. One evaluation, no bisection, no cap.
//! - **`refine`** is sign-change bisection on the same invariant, bounded by
//!   [`MAX_REFINE_STEPS`] so a pathological request declines rather than
//!   running away (the design note's "a slice that removes a bound must add
//!   one"). It returns whether the requested width was reached.
//! - **`enclosure`** rounds the two endpoints **outward** onto one dyadic grid
//!   with a single `axeyum-arith` call, so the caller never names a rounding
//!   direction and cannot name the wrong one for an endpoint.

use core::cmp::Ordering;

use axeyum_arith::big::{BigInt, BigRational, Sign};
use axeyum_arith::{AlgebraicNumber, Dyadic};

use crate::poly_big::BigAlgebraic;
use crate::real_algebraic::RealAlgebraic;

/// The largest number of bisection steps one [`AlgebraicNumber::refine`] call
/// will take.
///
/// Each step halves the interval, so this is 4 096 bits of width — far past
/// anything a witness needs, and a hard bound so a caller asking for an
/// impossible width gets `false` rather than a hang.
pub const MAX_REFINE_STEPS: u32 = 4_096;

/// The sign of a rational as an [`Ordering`] against zero.
fn rational_sign(value: &BigRational) -> Ordering {
    value.numer().sign().cmp(&Sign::NoSign)
}

/// `p(at)` for a least-significant-first integer polynomial, by Horner.
fn evaluate(poly: &[BigInt], at: &BigRational) -> BigRational {
    let mut accumulator = BigRational::from(BigInt::from(0));
    for coefficient in poly.iter().rev() {
        accumulator = accumulator * at + BigRational::from(coefficient.clone());
    }
    accumulator
}

/// The sign of the unique root of `poly` in `(lo, hi)`.
///
/// See the module doc: this is exact and runs no bisection.
fn root_sign(poly: &[BigInt], lo: &BigRational, hi: &BigRational) -> Ordering {
    if rational_sign(lo) != Ordering::Less {
        // lo >= 0, and the root is strictly greater than lo.
        return Ordering::Greater;
    }
    if rational_sign(hi) != Ordering::Greater {
        // hi <= 0, and the root is strictly less than hi.
        return Ordering::Less;
    }
    // lo < 0 < hi. The root is zero exactly when p(0) = 0.
    let at_zero = poly.first().map_or(Ordering::Equal, |constant| {
        constant.sign().cmp(&Sign::NoSign)
    });
    if at_zero == Ordering::Equal {
        return Ordering::Equal;
    }
    // The root lies in (lo, 0) iff p changes sign across that subinterval.
    let at_lo = rational_sign(&evaluate(poly, lo));
    if at_lo != Ordering::Equal {
        return if at_lo == at_zero {
            Ordering::Greater
        } else {
            Ordering::Less
        };
    }
    // A well-formed isolating interval has p(lo) != 0; fall back to the upper
    // endpoint rather than guessing.
    let at_hi = rational_sign(&evaluate(poly, hi));
    if at_hi == at_zero {
        Ordering::Less
    } else {
        Ordering::Greater
    }
}

/// One bisection pass: narrow `(lo, hi)` until it is at most `2^-bits` wide,
/// or until [`MAX_REFINE_STEPS`] is spent. Returns whether the width was
/// reached.
fn bisect(poly: &[BigInt], lo: &mut BigRational, hi: &mut BigRational, bits: u64) -> bool {
    if bits > u64::from(MAX_REFINE_STEPS) {
        // A width the step cap cannot buy. Decline rather than run away.
        return false;
    }
    let shift = u32::try_from(bits).unwrap_or(MAX_REFINE_STEPS);
    let target = BigRational::new(BigInt::from(1), BigInt::from(1) << shift);
    let two = BigRational::from(BigInt::from(2));
    let at_lo = rational_sign(&evaluate(poly, lo));
    let at_hi = rational_sign(&evaluate(poly, hi));
    if at_lo == Ordering::Equal || at_hi == Ordering::Equal || at_lo == at_hi {
        // Not a sign-change bracket: bisection has no invariant to preserve,
        // so decline rather than move the endpoints on a guess.
        return &*hi - &*lo <= target;
    }
    let mut steps = 0u32;
    while &*hi - &*lo > target {
        if steps >= MAX_REFINE_STEPS {
            return false;
        }
        steps += 1;
        let middle = (&*lo + &*hi) / &two;
        let at_middle = rational_sign(&evaluate(poly, &middle));
        if at_middle == Ordering::Equal {
            // The midpoint is the root exactly. Keep a bracket around it that
            // is at least as tight as the target and stop.
            let half = &target / &two;
            *lo = &middle - &half;
            *hi = &middle + &half;
            return true;
        }
        if at_middle == at_lo {
            *lo = middle;
        } else {
            *hi = middle;
        }
    }
    true
}

/// The largest `e` with `2^e ≤ width`, for a positive `width`.
///
/// Used to pick the dyadic grid an enclosure rounds onto: the grid step is at
/// most the interval's own width, so the outward rounding grows the interval by
/// at most a factor of three.
fn grid_exponent(width: &BigRational) -> i64 {
    let numerator = i64::try_from(width.numer().magnitude().bits()).unwrap_or(i64::MAX);
    let denominator = i64::try_from(width.denom().magnitude().bits()).unwrap_or(i64::MAX);
    numerator.saturating_sub(denominator).saturating_sub(1)
}

/// The outward dyadic enclosure of `(lo, hi)`.
fn enclose(lo: &BigRational, hi: &BigRational) -> Option<(Dyadic, Dyadic)> {
    let width = hi - lo;
    let exponent = if rational_sign(&width) == Ordering::Greater {
        grid_exponent(&width)
    } else {
        0
    };
    Dyadic::rationals_outward_at_exponent(lo, hi, exponent)
}

impl AlgebraicNumber for BigAlgebraic {
    fn sign(&self) -> Ordering {
        root_sign(&self.poly, &self.lo, &self.hi)
    }

    fn refine(&mut self, bits: u64) -> bool {
        bisect(&self.poly, &mut self.lo, &mut self.hi, bits)
    }

    fn enclosure(&self) -> Option<(Dyadic, Dyadic)> {
        enclose(&self.lo, &self.hi)
    }
}

impl AlgebraicNumber for RealAlgebraic {
    fn sign(&self) -> Ordering {
        let (lo, hi) = self.interval_big();
        root_sign(self.defining_poly(), &lo, &hi)
    }

    /// Refines through [`RealAlgebraic::new_big`], so the one-root invariant is
    /// re-established by the constructor rather than asserted by this module.
    /// A refinement the constructor refuses leaves the value untouched and
    /// reports `false`.
    fn refine(&mut self, bits: u64) -> bool {
        let (mut lo, mut hi) = self.interval_big();
        let poly = self.defining_poly().to_vec();
        let reached = bisect(&poly, &mut lo, &mut hi, bits);
        match RealAlgebraic::new_big(poly, lo, hi) {
            Some(refined) => {
                *self = refined;
                reached
            }
            None => false,
        }
    }

    fn enclosure(&self) -> Option<(Dyadic, Dyadic)> {
        let (lo, hi) = self.interval_big();
        enclose(&lo, &hi)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn poly(coefficients: &[i64]) -> Vec<BigInt> {
        coefficients.iter().map(|c| BigInt::from(*c)).collect()
    }

    /// √2 as `x² − 2` isolated in `(1, 2)`.
    fn root_two() -> BigAlgebraic {
        BigAlgebraic {
            poly: poly(&[-2, 0, 1]),
            lo: rat(1, 1),
            hi: rat(2, 1),
        }
    }

    /// −√2 as `x² − 2` isolated in `(−2, −1)`.
    fn minus_root_two() -> BigAlgebraic {
        BigAlgebraic {
            poly: poly(&[-2, 0, 1]),
            lo: rat(-2, 1),
            hi: rat(-1, 1),
        }
    }

    #[test]
    fn the_sign_is_decided_without_refinement_when_zero_is_outside() {
        assert_eq!(root_two().sign(), Ordering::Greater);
        assert_eq!(minus_root_two().sign(), Ordering::Less);
    }

    #[test]
    fn the_sign_is_decided_when_zero_is_inside_the_interval() {
        // x^2 - 2 isolated in (-3, 3) would hold two roots, so use a genuine
        // straddling case: 3x - 1 has its single root 1/3 in (-1, 1).
        let positive = BigAlgebraic {
            poly: poly(&[-1, 3]),
            lo: rat(-1, 1),
            hi: rat(1, 1),
        };
        assert_eq!(positive.sign(), Ordering::Greater);

        let negative = BigAlgebraic {
            poly: poly(&[1, 3]),
            lo: rat(-1, 1),
            hi: rat(1, 1),
        };
        assert_eq!(negative.sign(), Ordering::Less);

        // x itself: the root is zero, and p(0) = 0 says so with no bisection.
        let zero = BigAlgebraic {
            poly: poly(&[0, 1]),
            lo: rat(-1, 1),
            hi: rat(1, 1),
        };
        assert_eq!(zero.sign(), Ordering::Equal);
    }

    #[test]
    fn refinement_narrows_the_interval_and_still_contains_the_root() {
        let mut value = root_two();
        assert!(value.refine(20), "20 bits must be reachable");
        let width = &value.hi - &value.lo;
        assert!(width <= rat(1, 1 << 20), "width {width} is not below 2^-20");
        // √2 is still inside: 2 is between lo² and hi².
        let low_square = &value.lo * &value.lo;
        let high_square = &value.hi * &value.hi;
        assert!(low_square < rat(2, 1) && rat(2, 1) < high_square);
        assert_eq!(value.sign(), Ordering::Greater);
    }

    #[test]
    fn refinement_of_a_negative_root_keeps_its_sign() {
        let mut value = minus_root_two();
        assert!(value.refine(16));
        assert!(&value.hi - &value.lo <= rat(1, 1 << 16));
        assert!(value.hi < rat(0, 1));
        assert_eq!(value.sign(), Ordering::Less);
    }

    #[test]
    fn a_request_beyond_the_step_cap_is_declined_rather_than_hung() {
        let mut value = root_two();
        // One bit of width per step, so a request past the cap cannot be met.
        assert!(!value.refine(u64::from(MAX_REFINE_STEPS) + 10));
    }

    #[test]
    fn the_enclosure_contains_the_interval() {
        let mut value = root_two();
        assert!(value.refine(12));
        let (low, high) = value.enclosure().expect("an enclosure");
        assert!(
            low.to_rational() <= value.lo,
            "{low:?} is above the interval"
        );
        assert!(
            high.to_rational() >= value.hi,
            "{high:?} is below the interval"
        );
        // ...and it is not absurdly loose: at most three interval widths.
        let width = &value.hi - &value.lo;
        let enclosed = high.to_rational() - low.to_rational();
        assert!(enclosed <= &width * BigRational::from(BigInt::from(3)));
    }

    #[test]
    fn real_algebraic_agrees_with_big_algebraic_on_the_same_root() {
        let mut value =
            RealAlgebraic::new_big(poly(&[-2, 0, 1]), rat(1, 1), rat(2, 1)).expect("sqrt 2");
        assert_eq!(AlgebraicNumber::sign(&value), Ordering::Greater);
        assert!(value.refine(24));
        let (lo, hi) = value.interval_big();
        assert!(&hi - &lo <= rat(1, 1 << 24));
        let (low, high) = value.enclosure().expect("an enclosure");
        assert!(low.to_rational() <= lo && high.to_rational() >= hi);

        let mut negative =
            RealAlgebraic::new_big(poly(&[-2, 0, 1]), rat(-2, 1), rat(-1, 1)).expect("-sqrt 2");
        assert_eq!(AlgebraicNumber::sign(&negative), Ordering::Less);
        assert!(negative.refine(24));
        assert_eq!(AlgebraicNumber::sign(&negative), Ordering::Less);
    }

    #[test]
    fn a_rational_carried_as_an_algebraic_has_the_right_sign() {
        // 5/3 as 3x - 5, isolated in (1, 2).
        let value = RealAlgebraic::new_big(poly(&[-5, 3]), rat(1, 1), rat(2, 1)).expect("5/3");
        assert_eq!(AlgebraicNumber::sign(&value), Ordering::Greater);
        let negative = RealAlgebraic::new_big(poly(&[5, 3]), rat(-2, 1), rat(-1, 1)).expect("-5/3");
        assert_eq!(AlgebraicNumber::sign(&negative), Ordering::Less);
    }
}
