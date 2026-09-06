//! On-demand rational normalization: [`RawRational`] and its receipt.
//!
//! The design note's §3.2 leaves the normalization policy open and records why
//! the question is genuinely two-sided: GMP's *Rational Internals* argues for
//! **eager** reduction (*"a few small gcds immediately"* beat one big one
//! later), PARI measures the eager cost at 1 392 ms against 1 116 ms for one
//! degree-10³ squaring, Bernstein's balanced product tree is what makes
//! laziness asymptotically win, and CGAL's naive lazy DAG burned 501 MB
//! against 70 MB eager. ADR-1670's in-tree measurement is on the lazy side for
//! *our* shape: the integer ring beats `i128` rationals at degree 64 *"because
//! every `Rational::checked_mul` runs a Euclidean gcd to renormalize"*.
//!
//! So this module does not pick a winner by assertion. It provides the
//! **unreduced** carrier — arithmetic that never calls a gcd — together with a
//! [`NormalizationReceipt`] that records what the one deferred reduction
//! actually cost. A benchmark can then answer the policy question with a
//! number instead of a citation.
//!
//! The normal form is the usual one and is pinned by
//! [`NormalizationReceipt::verify`], not by comment: **the denominator is
//! strictly positive** (so the sign lives on the numerator), **the gcd of
//! numerator and denominator is one**, and **zero is `0/1`**.

use core::cmp::Ordering;

use num_bigint::{BigInt, BigUint, Sign};
use num_rational::BigRational;

use crate::Normalize;

/// What a [`Normalize::normalize`] call on a rational did.
///
/// Recorded rather than discarded because the whole argument for on-demand
/// normalization is that the gcds are rare; a receipt is how a benchmark finds
/// out whether they are.
///
/// The receipt also carries the four values the reduction ran between, which
/// is what makes [`NormalizationReceipt::verify`] a checker rather than a log
/// line: the two multiplications that re-derive the pre-normalization pair use
/// nothing the producer computed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalizationReceipt {
    /// The gcd that was divided out (one when the value was already reduced).
    pub common_factor: BigUint,
    /// Bits in the numerator before the reduction.
    pub numerator_bits_before: u64,
    /// Bits in the numerator after the reduction.
    pub numerator_bits_after: u64,
    /// The numerator before the reduction.
    pub numerator_before: BigInt,
    /// The denominator before the reduction. Never zero; may be negative,
    /// which is exactly the case the sign half of the policy exists for.
    pub denominator_before: BigInt,
    /// The numerator after the reduction.
    pub numerator_after: BigInt,
    /// The denominator after the reduction.
    pub denominator_after: BigInt,
}

impl NormalizationReceipt {
    /// Re-derive the reduction and check that the result is in normal form.
    ///
    /// Six conditions, each independently failable, and none of them trusting
    /// a number the producer computed:
    ///
    /// 1. the pre-reduction denominator is nonzero (there was a rational to
    ///    reduce at all);
    /// 2. the post-reduction denominator is **strictly positive** — this is
    ///    the sign half of the policy, and a `-3/-4` that reduced to `3/-4`
    ///    fails here while satisfying every other condition;
    /// 3. `common_factor` is nonzero;
    /// 4. the two claimed multiplications hold up to the sign the reduction is
    ///    allowed to move: `±common_factor · numerator_after = numerator_before`
    ///    and `±common_factor · denominator_after = denominator_before`, with
    ///    the **same** sign in both — a certificate that flipped the sign of
    ///    only one of the pair denotes a different rational and fails here;
    /// 5. the reduced pair is coprime — `common_factor` was the *whole* gcd,
    ///    not merely a common divisor. Condition 4 alone passes for any common
    ///    divisor, so this is the guard that pins the value;
    /// 6. the two recorded bit counts are the bit counts of the two recorded
    ///    numerators, so a benchmark reading them is reading a measurement.
    #[must_use]
    pub fn verify(&self) -> bool {
        if self.denominator_before.sign() == Sign::NoSign {
            return false;
        }
        if self.denominator_after.sign() != Sign::Plus {
            return false;
        }
        if self.common_factor.bits() == 0 {
            return false;
        }
        let factor = BigInt::from(self.common_factor.clone());
        let scaled_numerator = &factor * &self.numerator_after;
        let scaled_denominator = &factor * &self.denominator_after;
        let positive = scaled_numerator == self.numerator_before
            && scaled_denominator == self.denominator_before;
        let negative = -&scaled_numerator == self.numerator_before
            && -&scaled_denominator == self.denominator_before;
        if !(positive || negative) {
            return false;
        }
        if binary_gcd(
            self.numerator_after.magnitude(),
            self.denominator_after.magnitude(),
        ) != BigUint::from(1u8)
        {
            return false;
        }
        self.numerator_bits_before == self.numerator_before.magnitude().bits()
            && self.numerator_bits_after == self.numerator_after.magnitude().bits()
    }
}

/// A rational kept as an **unreduced** numerator/denominator pair.
///
/// Addition, subtraction, negation and multiplication run no gcd at all: they
/// are the schoolbook cross-multiplications, so a fold of `k` of them reaches
/// denominators of about `k·b` bits and pays for one reduction at the end
/// rather than `k` along the way. That is the trade the module doc prices.
///
/// The one invariant a `RawRational` always carries is that the denominator is
/// nonzero. It is **not** in normal form until [`Normalize::normalize`] is
/// called: the denominator may be negative and the pair may share a factor.
#[derive(Debug, Clone)]
pub struct RawRational {
    numerator: BigInt,
    denominator: BigInt,
}

impl RawRational {
    /// The unreduced rational `numerator / denominator`, or `None` when the
    /// denominator is zero.
    ///
    /// Nothing is reduced and no sign is moved — that is the point of the
    /// type, and [`Normalize::is_normalized`] will say so.
    pub fn new(numerator: BigInt, denominator: BigInt) -> Option<Self> {
        if denominator.sign() == Sign::NoSign {
            return None;
        }
        Some(Self {
            numerator,
            denominator,
        })
    }

    /// The integer `value` as `value / 1`, already in normal form.
    #[must_use]
    pub fn integer(value: BigInt) -> Self {
        Self {
            numerator: value,
            denominator: BigInt::from(1),
        }
    }

    /// Zero, as `0 / 1`.
    #[must_use]
    pub fn zero() -> Self {
        Self::integer(BigInt::from(0))
    }

    /// One, as `1 / 1`.
    #[must_use]
    pub fn one() -> Self {
        Self::integer(BigInt::from(1))
    }

    /// The value of a [`BigRational`], which `num-rational` already keeps
    /// reduced, so the result is in normal form.
    #[must_use]
    pub fn from_rational(value: &BigRational) -> Self {
        Self {
            numerator: value.numer().clone(),
            denominator: value.denom().clone(),
        }
    }

    /// The (possibly unreduced) numerator.
    #[must_use]
    pub fn numerator(&self) -> &BigInt {
        &self.numerator
    }

    /// The (possibly unreduced, possibly negative) denominator.
    #[must_use]
    pub fn denominator(&self) -> &BigInt {
        &self.denominator
    }

    /// Whether the value is zero. Cheap: a zero numerator over a nonzero
    /// denominator, no gcd.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.numerator.sign() == Sign::NoSign
    }

    /// The sum. **Runs no gcd**: `a/b + c/d = (ad + cb)/(bd)`.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self {
            numerator: &self.numerator * &other.denominator + &other.numerator * &self.denominator,
            denominator: &self.denominator * &other.denominator,
        }
    }

    /// The difference. Runs no gcd.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        self.add(&other.negated())
    }

    /// The negation. Runs no gcd.
    #[must_use]
    pub fn negated(&self) -> Self {
        Self {
            numerator: -self.numerator.clone(),
            denominator: self.denominator.clone(),
        }
    }

    /// The product. **Runs no gcd**: `(a/b)·(c/d) = (ac)/(bd)`, which is
    /// exactly the operation ADR-1670 measured a Euclidean gcd attached to.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        Self {
            numerator: &self.numerator * &other.numerator,
            denominator: &self.denominator * &other.denominator,
        }
    }

    /// The reciprocal, or `None` for zero. Runs no gcd.
    #[must_use]
    pub fn reciprocal(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        Some(Self {
            numerator: self.denominator.clone(),
            denominator: self.numerator.clone(),
        })
    }

    /// The exact value as a [`BigRational`]. This *does* reduce — that is what
    /// `BigRational` means — so it is one of the points the module doc names
    /// as a normalization site.
    #[must_use]
    pub fn to_rational(&self) -> BigRational {
        BigRational::new(self.numerator.clone(), self.denominator.clone())
    }

    /// Compare two unreduced rationals **without normalizing either**: one
    /// cross-multiplication and a sign, with the denominators' signs folded in.
    #[must_use]
    pub fn compare(&self, other: &Self) -> Ordering {
        let left = &self.numerator * &other.denominator;
        let right = &other.numerator * &self.denominator;
        let difference = left - right;
        let flip =
            (self.denominator.sign() == Sign::Minus) ^ (other.denominator.sign() == Sign::Minus);
        let order = difference.sign().cmp(&Sign::NoSign);
        if flip { order.reverse() } else { order }
    }

    /// A normalized copy, discarding the receipt.
    #[must_use]
    pub fn normalized(&self) -> Self {
        let mut copy = self.clone();
        let _ = copy.normalize();
        copy
    }
}

impl PartialEq for RawRational {
    /// Denotational equality: `1/2` and `2/4` are equal, and so are `1/2` and
    /// `-1/-2`. Derived equality would be wrong on an unreduced carrier, which
    /// is precisely why it is not derived.
    fn eq(&self, other: &Self) -> bool {
        self.compare(other) == Ordering::Equal
    }
}

impl Eq for RawRational {}

impl PartialOrd for RawRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RawRational {
    fn cmp(&self, other: &Self) -> Ordering {
        self.compare(other)
    }
}

impl Normalize for RawRational {
    type Receipt = NormalizationReceipt;

    fn normalize(&mut self) -> NormalizationReceipt {
        let numerator_before = self.numerator.clone();
        let denominator_before = self.denominator.clone();
        let numerator_bits_before = numerator_before.magnitude().bits();

        let common_factor =
            binary_gcd(numerator_before.magnitude(), denominator_before.magnitude());
        // `denominator_before` is nonzero by the type's invariant, so the gcd
        // is nonzero too and the divisions below are total.
        let divisor = BigInt::from(common_factor.clone());
        let mut numerator = &numerator_before / &divisor;
        let mut denominator = &denominator_before / &divisor;
        if denominator.sign() == Sign::Minus {
            numerator = -numerator;
            denominator = -denominator;
        }

        self.numerator.clone_from(&numerator);
        self.denominator.clone_from(&denominator);

        NormalizationReceipt {
            common_factor,
            numerator_bits_before,
            numerator_bits_after: numerator.magnitude().bits(),
            numerator_before,
            denominator_before,
            numerator_after: numerator,
            denominator_after: denominator,
        }
    }

    fn is_normalized(&self) -> bool {
        self.denominator.sign() == Sign::Plus
            && binary_gcd(self.numerator.magnitude(), self.denominator.magnitude())
                == BigUint::from(1u8)
    }
}

/// The gcd of two magnitudes, by the binary (Stein) algorithm.
///
/// Written here rather than pulled from `num-integer` for the reason ADR-1710
/// gives for this crate existing at all: `axeyum-arith` is the one place the
/// workspace names its arithmetic dependencies. `gcd(0, 0)` is `0`, which
/// [`NormalizationReceipt::verify`] rejects through its nonzero-factor guard
/// rather than by dividing by it.
pub(crate) fn binary_gcd(left: &BigUint, right: &BigUint) -> BigUint {
    let mut a = left.clone();
    let mut b = right.clone();
    if a.bits() == 0 {
        return b;
    }
    if b.bits() == 0 {
        return a;
    }
    let shift = a
        .trailing_zeros()
        .unwrap_or(0)
        .min(b.trailing_zeros().unwrap_or(0));
    a >>= a.trailing_zeros().unwrap_or(0);
    loop {
        b >>= b.trailing_zeros().unwrap_or(0);
        if a > b {
            core::mem::swap(&mut a, &mut b);
        }
        b -= &a;
        if b.bits() == 0 {
            break;
        }
    }
    a << shift
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(value: i64) -> BigInt {
        BigInt::from(value)
    }

    fn raw(numerator: i64, denominator: i64) -> RawRational {
        RawRational::new(big(numerator), big(denominator)).expect("nonzero denominator")
    }

    #[test]
    fn a_zero_denominator_is_refused() {
        assert!(RawRational::new(big(1), big(0)).is_none());
        assert!(RawRational::new(big(0), big(0)).is_none());
        assert!(RawRational::new(big(1), big(-1)).is_some());
    }

    #[test]
    fn arithmetic_leaves_the_pair_unreduced() {
        // 1/2 + 1/2: the reduced answer is 1/1, but the unreduced carrier is
        // required to hand back 4/4 -- that is the whole measurement.
        let sum = raw(1, 2).add(&raw(1, 2));
        assert_eq!(sum.numerator(), &big(4));
        assert_eq!(sum.denominator(), &big(4));
        assert!(!sum.is_normalized());
        // ...while still denoting one.
        assert_eq!(sum, raw(1, 1));
    }

    #[test]
    fn a_product_runs_no_gcd() {
        let product = raw(6, 10).mul(&raw(15, 4));
        assert_eq!(product.numerator(), &big(90));
        assert_eq!(product.denominator(), &big(40));
        assert_eq!(product.to_rational(), BigRational::new(big(9), big(4)));
    }

    #[test]
    fn normalization_puts_the_sign_on_the_numerator() {
        let mut value = raw(3, -4);
        let receipt = value.normalize();
        assert_eq!(value.numerator(), &big(-3));
        assert_eq!(value.denominator(), &big(4));
        assert!(value.is_normalized());
        assert!(receipt.verify());

        // Both negative: the sign cancels rather than moving.
        let mut value = raw(-3, -4);
        let receipt = value.normalize();
        assert_eq!(value.numerator(), &big(3));
        assert_eq!(value.denominator(), &big(4));
        assert!(receipt.verify());
    }

    #[test]
    fn normalization_divides_out_the_whole_gcd_and_reports_it() {
        let mut value = raw(84, -36);
        let receipt = value.normalize();
        assert_eq!(receipt.common_factor, BigUint::from(12u8));
        assert_eq!(value.numerator(), &big(-7));
        assert_eq!(value.denominator(), &big(3));
        assert_eq!(receipt.numerator_bits_before, 7); // 84 = 0b1010100
        assert_eq!(receipt.numerator_bits_after, 3); // 7 = 0b111
        assert!(receipt.verify());
    }

    #[test]
    fn normalizing_an_already_reduced_value_reports_a_unit_factor() {
        let mut value = raw(7, 3);
        let receipt = value.normalize();
        assert_eq!(receipt.common_factor, BigUint::from(1u8));
        assert_eq!(receipt.numerator_bits_before, receipt.numerator_bits_after);
        assert!(receipt.verify());
        assert!(value.is_normalized());
    }

    #[test]
    fn zero_normalizes_to_zero_over_one() {
        let mut value = raw(0, -5);
        let receipt = value.normalize();
        assert_eq!(value.numerator(), &big(0));
        assert_eq!(value.denominator(), &big(1));
        assert_eq!(receipt.common_factor, BigUint::from(5u8));
        assert!(receipt.verify());
        assert!(value.is_normalized());
    }

    #[test]
    fn a_lazy_fold_and_an_eager_fold_agree_on_the_value() {
        // The policy question in one test: fold twelve fractions with no gcd
        // at all, normalize once, and check against `BigRational`, which runs
        // a gcd on every step.
        let mut lazy = RawRational::one();
        let mut eager = BigRational::from(big(1));
        for index in 1..=12i64 {
            let term = raw(index, index + 7);
            lazy = lazy.mul(&term);
            eager *= BigRational::new(big(index), big(index + 7));
        }
        assert!(
            !lazy.is_normalized(),
            "the lazy fold must still be unreduced"
        );
        let receipt = lazy.normalize();
        assert!(receipt.verify());
        assert!(
            receipt.numerator_bits_after < receipt.numerator_bits_before,
            "the deferred gcd must actually shrink the numerator: {} -> {}",
            receipt.numerator_bits_before,
            receipt.numerator_bits_after
        );
        assert_eq!(lazy.to_rational(), eager);
    }

    #[test]
    fn comparison_does_not_normalize_and_handles_negative_denominators() {
        let half = raw(1, 2);
        let also_half = raw(-50, -100);
        assert_eq!(half.compare(&also_half), Ordering::Equal);
        assert!(!also_half.is_normalized());
        assert_eq!(raw(1, 3).compare(&raw(1, 2)), Ordering::Less);
        assert_eq!(raw(1, -3).compare(&raw(1, 2)), Ordering::Less);
        assert_eq!(raw(-1, 3).compare(&raw(1, -2)), Ordering::Greater);
        let mut values = [raw(3, -4), raw(1, 8), raw(0, 9), raw(5, 2)];
        values.sort();
        let ordered: Vec<BigRational> = values.iter().map(RawRational::to_rational).collect();
        for pair in ordered.windows(2) {
            assert!(pair[0] <= pair[1]);
        }
    }

    #[test]
    fn reciprocal_of_zero_is_refused() {
        assert!(RawRational::zero().reciprocal().is_none());
        let inverse = raw(-2, 6).reciprocal().unwrap();
        assert_eq!(inverse.to_rational(), BigRational::new(big(-3), big(1)));
    }

    #[test]
    fn forged_normalization_receipts_all_fail_verification() {
        let mut honest_value = raw(84, -36);
        let honest = honest_value.normalize();
        assert!(honest.verify());

        // 1. A zero pre-reduction denominator: there was no rational.
        let forged = NormalizationReceipt {
            denominator_before: big(0),
            ..honest.clone()
        };
        assert!(!forged.verify(), "a zero denominator must be caught");

        // 2. The sign left on the denominator. Every multiplication still
        //    holds -- only the sign half of the policy is violated.
        let forged = NormalizationReceipt {
            numerator_after: big(7),
            denominator_after: big(-3),
            ..honest.clone()
        };
        assert!(!forged.verify(), "a negative denominator must be caught");

        // 3. A common divisor that is not the whole gcd: 6 divides both, and
        //    both multiplications hold, so the product guard passes and only
        //    the coprimality guard can reject it.
        let forged = NormalizationReceipt {
            common_factor: BigUint::from(6u8),
            numerator_after: big(-14),
            denominator_after: big(6),
            numerator_bits_after: 4,
            ..honest.clone()
        };
        assert!(
            !forged.verify(),
            "a partial reduction must be caught even though its products hold"
        );

        // 4. A sign flipped on one side of the pair only: the value changes.
        let forged = NormalizationReceipt {
            numerator_after: big(7),
            ..honest.clone()
        };
        assert!(!forged.verify(), "a one-sided sign flip must be caught");

        // 5. A tampered bit count, with every value correct.
        let forged = NormalizationReceipt {
            numerator_bits_after: 99,
            ..honest.clone()
        };
        assert!(!forged.verify(), "a tampered bit count must be caught");

        // 6. A zero common factor.
        let forged = NormalizationReceipt {
            common_factor: BigUint::from(0u8),
            ..honest.clone()
        };
        assert!(!forged.verify(), "a zero common factor must be caught");
    }

    #[test]
    fn the_binary_gcd_agrees_with_a_euclidean_reference_over_a_sweep() {
        fn euclid(mut a: BigUint, mut b: BigUint) -> BigUint {
            while b.bits() != 0 {
                let r = &a % &b;
                a = b;
                b = r;
            }
            a
        }
        for left in 0u64..40 {
            for right in 0u64..40 {
                let a = BigUint::from(left);
                let b = BigUint::from(right);
                assert_eq!(
                    binary_gcd(&a, &b),
                    euclid(a.clone(), b.clone()),
                    "gcd({left}, {right})"
                );
            }
        }
        // Past `u128`, which is why this crate exists.
        let a = (BigUint::from(1u8) << 200u8) - BigUint::from(1u8);
        let b = (BigUint::from(1u8) << 120u8) - BigUint::from(1u8);
        assert_eq!(binary_gcd(&a, &b), euclid(a.clone(), b.clone()));
    }
}
