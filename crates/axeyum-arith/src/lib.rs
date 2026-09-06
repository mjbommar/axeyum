//! `axeyum-arith` — the shared exact-arithmetic layer.
//!
//! This crate is the single place the workspace keeps exact arithmetic that is
//! wider than a machine word: dyadic rationals with directed rounding,
//! certified positional (radix) expansions, arbitrary-precision rationals with
//! an explicit normalization policy, univariate polynomials over ℤ and ℚ with
//! fraction-free operations, modular rings, `p`-adic lifting, and algebraic
//! numbers.
//!
//! The design note is `docs/research/10-cas/axeyum-arith-design.md` and the
//! decision is ADR-1710. In one sentence: eight separate univariate
//! polynomial-over-ℚ implementations exist across `axeyum-cas` and
//! `axeyum-ir`, five of them over `BigRational`, and this crate is where the
//! ninth does not get written.
//!
//! # What is implemented here today
//!
//! [`Dyadic`]; the radix types ([`Radix`], [`RadixCertificate`], [`MixedRadix`],
//! [`MixedRadixCertificate`]); and, since migration slice 2,
//! [`ModularRing`]/[`PlainModRing`] and [`PowModCertificate`]. Everything else
//! in this file is a **signature sketch**: traits with no bodies, and
//! certificate structs whose `verify` is `todo!()`. That is deliberate — the
//! sketch is what makes the design compile-checked without pre-empting the
//! migration lanes that will implement it against the copies they replace.
//!
//! # Two standing rules
//!
//! - **No C or C++ dependency, and the crate builds for `wasm32`.** The only
//!   dependencies are `num-bigint` and `num-rational`, both pure Rust.
//! - **An operation that a caller could re-derive returns a certificate that
//!   the caller can re-derive.** [`RadixCertificate::verify`] is the worked
//!   example: it evaluates the digits in the base and compares, using nothing
//!   the producer computed.

use core::cmp::Ordering;

use num_bigint::{BigInt, BigUint, Sign};
use num_rational::BigRational;

pub mod upoly;

pub use upoly::{
    DEFAULT_ISOLATION_STEPS, PolyBezoutCertificate, PolyGcdCertificate, QPoly, SturmChain, ZPoly,
    count_real_roots, count_real_roots_in, evaluate_slice, extended_gcd, isolate_real_roots,
    sign_at_slice, sign_of_rational, sign_variations_rational, slice_degree, trim_coefficients,
};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// The largest exponent magnitude a [`Dyadic`] may carry.
///
/// Bounded well inside `i64` so that normalization, rounding and
/// multiplication can adjust an exponent without an overflow check at every
/// step; a value outside this range cannot be materialized on any machine.
pub const MAX_EXPONENT: i64 = 1 << 62;

/// The largest alignment shift [`Dyadic::checked_add`] will perform.
///
/// Adding two dyadics whose exponents differ by `d` builds a mantissa with
/// roughly `d` extra bits. `2^32` bits is 512 MiB of mantissa; past that the
/// addition declines rather than allocating. This is the crate's **width
/// contract**: an exact operation either answers or says how it would have
/// exceeded its budget, never silently rounds.
pub const MAX_ALIGN_BITS: u64 = 1 << 32;

fn bits_as_i64(bits: u64) -> Option<i64> {
    i64::try_from(bits).ok()
}

// ---------------------------------------------------------------------------
// Dyadic rationals
// ---------------------------------------------------------------------------

/// A rounding direction.
///
/// [`Round::Down`] and [`Round::Up`] are the *outward* pair for an interval:
/// round a lower endpoint [`Round::Down`] and an upper endpoint
/// [`Round::Up`] and the rounded interval contains the exact one. See
/// [`Dyadic::round_outward`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Round {
    /// Toward negative infinity (floor).
    Down,
    /// Toward positive infinity (ceiling).
    Up,
    /// Toward zero (truncate the magnitude).
    TowardZero,
    /// Away from zero (grow the magnitude).
    AwayFromZero,
    /// To the nearest representable value; exact ties go to the even mantissa.
    NearestTiesToEven,
}

/// An exact dyadic rational `mantissa · 2^exponent`.
///
/// The representation is **canonical**: the mantissa of a nonzero value is
/// odd, and zero is `(0, 0)`. So derived `PartialEq`/`Eq`/`Hash` agree with
/// [`Ord`], and two dyadics are equal exactly when they denote the same
/// rational. Addition, subtraction and multiplication are exact; rounding is
/// the only lossy operation and it is always explicit about its direction.
///
/// This is the representation the CAS's validated-numerics layer wants
/// underneath its intervals: a dyadic interval's endpoints are exactly
/// representable, its outward rounding is a shift, and converting to
/// [`BigRational`] for a proof obligation is exact.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Dyadic {
    mantissa: BigInt,
    exponent: i64,
}

impl Dyadic {
    /// The dyadic `mantissa · 2^exponent`, normalized to an odd mantissa.
    ///
    /// Returns `None` if `exponent` is outside `±`[`MAX_EXPONENT`], or if
    /// stripping the mantissa's trailing zero bits would push the exponent
    /// outside that range.
    pub fn new(mantissa: BigInt, exponent: i64) -> Option<Self> {
        if !(-MAX_EXPONENT..=MAX_EXPONENT).contains(&exponent) {
            return None;
        }
        if mantissa.sign() == Sign::NoSign {
            return Some(Self {
                mantissa: BigInt::from(0),
                exponent: 0,
            });
        }
        let shift = mantissa.magnitude().trailing_zeros().unwrap_or(0);
        let exponent = exponent.checked_add(bits_as_i64(shift)?)?;
        if !(-MAX_EXPONENT..=MAX_EXPONENT).contains(&exponent) {
            return None;
        }
        Some(Self {
            mantissa: mantissa >> shift,
            exponent,
        })
    }

    /// The dyadic zero.
    pub fn zero() -> Self {
        Self {
            mantissa: BigInt::from(0),
            exponent: 0,
        }
    }

    /// The dyadic denoting the integer `value`.
    pub fn from_i64(value: i64) -> Self {
        // `0` is inside the exponent range and the mantissa is finite, so the
        // only `None` case of `new` cannot arise here.
        Self::new(BigInt::from(value), 0).unwrap_or_else(Self::zero)
    }

    /// The odd mantissa (zero for the dyadic zero).
    pub fn mantissa(&self) -> &BigInt {
        &self.mantissa
    }

    /// The exponent (zero for the dyadic zero).
    pub fn exponent(&self) -> i64 {
        self.exponent
    }

    /// Whether this is the dyadic zero.
    pub fn is_zero(&self) -> bool {
        self.mantissa.sign() == Sign::NoSign
    }

    /// The number of significant bits: the bit length of the odd mantissa.
    ///
    /// Zero has zero significant bits. This is the quantity
    /// [`Dyadic::round`] bounds.
    pub fn precision_bits(&self) -> u64 {
        self.mantissa.magnitude().bits()
    }

    /// The negation. Exact, and never fails: negating an odd mantissa keeps it
    /// odd, so the exponent does not move.
    #[must_use]
    pub fn negate(&self) -> Self {
        Self {
            mantissa: -self.mantissa.clone(),
            exponent: self.exponent,
        }
    }

    /// The absolute value. Exact, and never fails, for the same reason as
    /// [`Dyadic::negate`].
    #[must_use]
    pub fn abs(&self) -> Self {
        if self.mantissa.sign() == Sign::Minus {
            self.negate()
        } else {
            self.clone()
        }
    }

    /// The number of bits the mantissa of `self + other` would occupy before
    /// normalization, or `None` if the two exponents are too far apart to
    /// align inside [`MAX_ALIGN_BITS`].
    ///
    /// Call this before [`Dyadic::checked_add`] when the budget matters; the
    /// addition itself applies the same bound.
    pub fn align_cost_bits(&self, other: &Self) -> Option<u64> {
        let gap = i128::from(self.exponent) - i128::from(other.exponent);
        let gap = u64::try_from(gap.abs()).ok()?;
        if gap > MAX_ALIGN_BITS {
            return None;
        }
        Some(gap + self.precision_bits().max(other.precision_bits()))
    }

    /// The exact sum, or `None` if the alignment shift would exceed
    /// [`MAX_ALIGN_BITS`] or the result's exponent would leave
    /// `±`[`MAX_EXPONENT`].
    pub fn checked_add(&self, other: &Self) -> Option<Self> {
        if self.is_zero() {
            return Some(other.clone());
        }
        if other.is_zero() {
            return Some(self.clone());
        }
        let exponent = self.exponent.min(other.exponent);
        let lhs_shift = u64::try_from(i128::from(self.exponent) - i128::from(exponent)).ok()?;
        let rhs_shift = u64::try_from(i128::from(other.exponent) - i128::from(exponent)).ok()?;
        if lhs_shift > MAX_ALIGN_BITS || rhs_shift > MAX_ALIGN_BITS {
            return None;
        }
        let sum = (&self.mantissa << lhs_shift) + (&other.mantissa << rhs_shift);
        Self::new(sum, exponent)
    }

    /// The exact difference. Same failure conditions as
    /// [`Dyadic::checked_add`].
    pub fn checked_sub(&self, other: &Self) -> Option<Self> {
        self.checked_add(&other.negate())
    }

    /// The exact product, or `None` if the result's exponent would leave
    /// `±`[`MAX_EXPONENT`].
    ///
    /// A product needs no alignment, so it has no width budget: the mantissa
    /// is the product of two odd mantissas, which is odd, so the result is
    /// already normalized.
    pub fn checked_mul(&self, other: &Self) -> Option<Self> {
        if self.is_zero() || other.is_zero() {
            return Some(Self::zero());
        }
        let exponent = self.exponent.checked_add(other.exponent)?;
        Self::new(&self.mantissa * &other.mantissa, exponent)
    }

    /// This dyadic rounded to at most `precision_bits` significant bits in the
    /// direction `mode`.
    ///
    /// Returns `self` unchanged when it already fits. Returns `None` when
    /// `precision_bits` is zero or the exponent would leave
    /// `±`[`MAX_EXPONENT`].
    pub fn round(&self, precision_bits: u64, mode: Round) -> Option<Self> {
        if precision_bits == 0 {
            return None;
        }
        let bits = self.precision_bits();
        if bits <= precision_bits {
            return Some(self.clone());
        }
        let dropped = bits - precision_bits;
        let sign = self.mantissa.sign();
        let original = self.mantissa.magnitude();
        let quotient = original >> dropped;
        let remainder = original - (&quotient << dropped);
        let magnitude = if wants_increment(&remainder, dropped, sign, &quotient, mode) {
            quotient + BigUint::from(1u8)
        } else {
            quotient
        };
        let exponent = self.exponent.checked_add(bits_as_i64(dropped)?)?;
        Self::new(BigInt::from_biguint(sign, magnitude), exponent)
    }

    /// Round an interval `[lower, upper]` outward to `precision_bits`.
    ///
    /// The returned pair contains the input interval: the lower endpoint moves
    /// toward `-∞` and the upper toward `+∞`. This is the only rounding an
    /// enclosure is allowed to do, and having it as one call is what stops a
    /// caller from rounding both endpoints the same way by accident — the
    /// defect class the CAS's `enclosure.rs` has to guard against by hand.
    pub fn round_outward(lower: &Self, upper: &Self, precision_bits: u64) -> Option<(Self, Self)> {
        let low = lower.round(precision_bits, Round::Down)?;
        let high = upper.round(precision_bits, Round::Up)?;
        Some((low, high))
    }

    /// The exact value as a [`BigRational`].
    pub fn to_rational(&self) -> BigRational {
        if self.exponent >= 0 {
            let shift = u64::try_from(self.exponent).unwrap_or(0);
            BigRational::from(&self.mantissa << shift)
        } else {
            let shift = u64::try_from(-self.exponent).unwrap_or(0);
            BigRational::new(self.mantissa.clone(), BigInt::from(1) << shift)
        }
    }

    /// The rational `value` rounded to at most `precision_bits` significant
    /// bits in the direction `mode`.
    ///
    /// The rounding is applied **once**, at the position the result needs, so
    /// there is no double rounding: `NearestTiesToEven` here means nearest to
    /// the exact rational, not nearest to some wider intermediate.
    ///
    /// Returns `None` if `precision_bits` is zero or the exponent leaves
    /// `±`[`MAX_EXPONENT`].
    pub fn from_rational(value: &BigRational, precision_bits: u64, mode: Round) -> Option<Self> {
        if precision_bits == 0 {
            return None;
        }
        let sign = value.numer().sign();
        if sign == Sign::NoSign {
            return Some(Self::zero());
        }
        let numerator = value.numer().magnitude().clone();
        let denominator = value.denom().magnitude().clone();
        let scale = bits_as_i64(numerator.bits())?
            .checked_sub(bits_as_i64(denominator.bits())?)?
            .checked_sub(bits_as_i64(precision_bits)?)?;
        let (quotient, remainder, divisor, scale) =
            scaled_divide(&numerator, &denominator, scale, precision_bits)?;
        let magnitude = if wants_increment_ratio(&remainder, &divisor, sign, &quotient, mode) {
            quotient + BigUint::from(1u8)
        } else {
            quotient
        };
        Self::new(BigInt::from_biguint(sign, magnitude), scale)
    }
}

impl Ord for Dyadic {
    fn cmp(&self, other: &Self) -> Ordering {
        // Cheap sign comparison first; it decides most pairs without a shift.
        let sign_order = self.mantissa.sign().cmp(&other.mantissa.sign());
        if sign_order != Ordering::Equal {
            return sign_order;
        }
        if let Some(difference) = self.checked_sub(other) {
            difference.mantissa.sign().cmp(&Sign::NoSign)
        } else {
            // The alignment budget was exceeded, which can only happen when the
            // exponents differ by more than `MAX_ALIGN_BITS`. At that distance
            // the larger exponent dominates for a same-signed pair, reversed
            // when both are negative.
            let by_exponent = self.exponent.cmp(&other.exponent);
            if self.mantissa.sign() == Sign::Minus {
                by_exponent.reverse()
            } else {
                by_exponent
            }
        }
    }
}

impl PartialOrd for Dyadic {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn wants_increment(
    remainder: &BigUint,
    dropped: u64,
    sign: Sign,
    quotient: &BigUint,
    mode: Round,
) -> bool {
    if remainder.bits() == 0 {
        return false;
    }
    match mode {
        Round::TowardZero => false,
        Round::AwayFromZero => true,
        Round::Down => sign == Sign::Minus,
        Round::Up => sign == Sign::Plus,
        Round::NearestTiesToEven => {
            let half = BigUint::from(1u8) << (dropped - 1);
            match remainder.cmp(&half) {
                Ordering::Less => false,
                Ordering::Greater => true,
                Ordering::Equal => quotient.bit(0),
            }
        }
    }
}

fn wants_increment_ratio(
    remainder: &BigUint,
    divisor: &BigUint,
    sign: Sign,
    quotient: &BigUint,
    mode: Round,
) -> bool {
    if remainder.bits() == 0 {
        return false;
    }
    match mode {
        Round::TowardZero => false,
        Round::AwayFromZero => true,
        Round::Down => sign == Sign::Minus,
        Round::Up => sign == Sign::Plus,
        Round::NearestTiesToEven => match (remainder << 1u8).cmp(divisor) {
            Ordering::Less => false,
            Ordering::Greater => true,
            Ordering::Equal => quotient.bit(0),
        },
    }
}

/// Divide `numerator / denominator / 2^scale`, correcting `scale` once so the
/// quotient has exactly `precision_bits` bits.
///
/// Returns `(quotient, remainder, divisor, scale)`, where the exact value is
/// `(quotient + remainder/divisor) · 2^scale`.
fn scaled_divide(
    numerator: &BigUint,
    denominator: &BigUint,
    scale: i64,
    precision_bits: u64,
) -> Option<(BigUint, BigUint, BigUint, i64)> {
    let (quotient, remainder, divisor) = divide_at_scale(numerator, denominator, scale)?;
    if quotient.bits() <= precision_bits {
        return Some((quotient, remainder, divisor, scale));
    }
    // `numerator/denominator` lies in `[2^(bn-bd-1), 2^(bn-bd+1))`, so the
    // first quotient has `precision_bits` or `precision_bits + 1` bits and one
    // correction is enough.
    let correction = bits_as_i64(quotient.bits() - precision_bits)?;
    let scale = scale.checked_add(correction)?;
    let (quotient, remainder, divisor) = divide_at_scale(numerator, denominator, scale)?;
    Some((quotient, remainder, divisor, scale))
}

fn divide_at_scale(
    numerator: &BigUint,
    denominator: &BigUint,
    scale: i64,
) -> Option<(BigUint, BigUint, BigUint)> {
    let (dividend, divisor) = if scale >= 0 {
        let shift = u64::try_from(scale).ok()?;
        (numerator.clone(), denominator << shift)
    } else {
        let shift = u64::try_from(-scale).ok()?;
        (numerator << shift, denominator.clone())
    };
    let quotient = &dividend / &divisor;
    let remainder = dividend - &quotient * &divisor;
    Some((quotient, remainder, divisor))
}

// ---------------------------------------------------------------------------
// Radix: certified positional notation
// ---------------------------------------------------------------------------

/// A positional numeral system in a fixed base `b ≥ 2`.
///
/// The base is a [`BigUint`], not a `u32`, so `2^64` and `10^9` are as valid
/// as `10` — a big base is how a divide-and-conquer conversion and the
/// kernel bridge's `2^k` limb chain both want to be spelled.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Radix {
    base: BigUint,
}

impl Radix {
    /// The numeral system in base `base`, or `None` if `base < 2`.
    pub fn new(base: BigUint) -> Option<Self> {
        if base < BigUint::from(2u8) {
            return None;
        }
        Some(Self { base })
    }

    /// The base.
    pub fn base(&self) -> &BigUint {
        &self.base
    }

    /// The canonical positional expansion of `value`, with its certificate.
    ///
    /// Digits are little-endian (index `i` carries `base^i`) and canonical:
    /// the most significant digit is nonzero, and zero expands to the empty
    /// digit list.
    ///
    /// The expansion is a repeated division, so it is quadratic in the digit
    /// count. That is the right first implementation and the wrong final one:
    /// the design note records Bernstein's divide-and-conquer conversion as
    /// the replacement, and [`RadixCertificate::verify`] is what makes the
    /// replacement safe to make.
    pub fn expand(&self, value: &BigUint) -> RadixCertificate {
        let mut digits = Vec::new();
        let mut rest = value.clone();
        while rest.bits() != 0 {
            let quotient = &rest / &self.base;
            let digit = rest - &quotient * &self.base;
            digits.push(digit);
            rest = quotient;
        }
        RadixCertificate {
            base: self.base.clone(),
            digits,
            value: value.clone(),
        }
    }

    /// Evaluate a little-endian digit list in this base by Horner's rule, or
    /// `None` if some digit is not less than the base.
    ///
    /// Leading zero digits are accepted here; canonicality is
    /// [`RadixCertificate::verify`]'s business, not evaluation's.
    pub fn evaluate(&self, digits: &[BigUint]) -> Option<BigUint> {
        let mut accumulator = BigUint::from(0u8);
        for digit in digits.iter().rev() {
            if digit >= &self.base {
                return None;
            }
            accumulator = accumulator * &self.base + digit;
        }
        Some(accumulator)
    }
}

/// A claim that `value` has the little-endian digits `digits` in base `base`.
///
/// The point of the type is [`RadixCertificate::verify`], which re-derives
/// the value from the digits by evaluation and compares. Nothing the producer
/// computed is trusted, so a fast conversion (divide-and-conquer, a cached
/// power table, an FFI shortcut) is checked by the same three lines as the
/// schoolbook one.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RadixCertificate {
    base: BigUint,
    digits: Vec<BigUint>,
    value: BigUint,
}

impl RadixCertificate {
    /// Assemble a certificate from parts, **without checking it**.
    ///
    /// This is the constructor for a certificate that arrives from somewhere
    /// else — a serialized artifact, a faster converter, another process.
    /// Call [`RadixCertificate::verify`] before believing it.
    pub fn from_parts(base: BigUint, digits: Vec<BigUint>, value: BigUint) -> Self {
        Self {
            base,
            digits,
            value,
        }
    }

    /// The base.
    pub fn base(&self) -> &BigUint {
        &self.base
    }

    /// The little-endian digits.
    pub fn digits(&self) -> &[BigUint] {
        &self.digits
    }

    /// The claimed value.
    pub fn value(&self) -> &BigUint {
        &self.value
    }

    /// Re-derive the value from the digits and compare.
    ///
    /// Four conditions, each of which a forged certificate can fail
    /// independently: the base is at least two; every digit is less than the
    /// base; the expansion is canonical (no zero in the most significant
    /// position); and Horner evaluation of the digits reproduces `value`.
    pub fn verify(&self) -> bool {
        if self.base < BigUint::from(2u8) {
            return false;
        }
        if let Some(most_significant) = self.digits.last()
            && most_significant.bits() == 0
        {
            return false;
        }
        let mut accumulator = BigUint::from(0u8);
        for digit in self.digits.iter().rev() {
            if digit >= &self.base {
                return false;
            }
            accumulator = accumulator * &self.base + digit;
        }
        accumulator == self.value
    }
}

/// A mixed-radix numeral system: position `i` carries the weight
/// `bases[0] · … · bases[i-1]`.
///
/// Mixed radix is what a CRT reconstruction, a factorial number system and a
/// bounded odometer all are, and it is the representation a per-prime residue
/// certificate wants to be checked against.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MixedRadix {
    bases: Vec<BigUint>,
}

impl MixedRadix {
    /// The mixed-radix system with the given per-position bases, or `None` if
    /// the list is empty or some base is less than two.
    pub fn new(bases: Vec<BigUint>) -> Option<Self> {
        if bases.is_empty() || bases.iter().any(|base| base < &BigUint::from(2u8)) {
            return None;
        }
        Some(Self { bases })
    }

    /// The per-position bases.
    pub fn bases(&self) -> &[BigUint] {
        &self.bases
    }

    /// The product of the bases: the number of values the system represents.
    pub fn modulus(&self) -> BigUint {
        let mut product = BigUint::from(1u8);
        for base in &self.bases {
            product *= base;
        }
        product
    }

    /// The mixed-radix expansion of `value`, or `None` if `value` is at least
    /// [`MixedRadix::modulus`].
    pub fn expand(&self, value: &BigUint) -> Option<MixedRadixCertificate> {
        if value >= &self.modulus() {
            return None;
        }
        let mut digits = Vec::with_capacity(self.bases.len());
        let mut rest = value.clone();
        for base in &self.bases {
            let quotient = &rest / base;
            let digit = rest - &quotient * base;
            digits.push(digit);
            rest = quotient;
        }
        Some(MixedRadixCertificate {
            bases: self.bases.clone(),
            digits,
            value: value.clone(),
        })
    }
}

/// A claim that `value` has the mixed-radix digits `digits` under `bases`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MixedRadixCertificate {
    bases: Vec<BigUint>,
    digits: Vec<BigUint>,
    value: BigUint,
}

impl MixedRadixCertificate {
    /// Assemble a certificate from parts, **without checking it**. See
    /// [`RadixCertificate::from_parts`].
    pub fn from_parts(bases: Vec<BigUint>, digits: Vec<BigUint>, value: BigUint) -> Self {
        Self {
            bases,
            digits,
            value,
        }
    }

    /// The per-position bases.
    pub fn bases(&self) -> &[BigUint] {
        &self.bases
    }

    /// The digits, least significant first.
    pub fn digits(&self) -> &[BigUint] {
        &self.digits
    }

    /// The claimed value.
    pub fn value(&self) -> &BigUint {
        &self.value
    }

    /// Re-derive the value from the digits and weights and compare.
    pub fn verify(&self) -> bool {
        if self.bases.len() != self.digits.len() || self.bases.is_empty() {
            return false;
        }
        let mut weight = BigUint::from(1u8);
        let mut accumulator = BigUint::from(0u8);
        for (base, digit) in self.bases.iter().zip(&self.digits) {
            if base < &BigUint::from(2u8) || digit >= base {
                return false;
            }
            accumulator += digit * &weight;
            weight *= base;
        }
        accumulator == self.value
    }
}

// ---------------------------------------------------------------------------
// Signature sketch: everything below has no implementation in this crate yet
// ---------------------------------------------------------------------------

/// The normalization policy for a value that can be kept unreduced.
///
/// A `BigRat` that reduces on every operation pays a Euclidean gcd per
/// multiplication; ADR-1670's measurement of the CAS zero test attributes the
/// `i128` rational's loss at degree 64 to exactly that. The policy this crate
/// adopts is **normalize on demand**: arithmetic accumulates an unreduced
/// numerator and denominator, and the caller asks for a normal form at the
/// points where one is needed — a comparison, a hash, a serialization, a
/// certificate.
///
/// [`Normalize::normalize`] returns a receipt so that "was this normalized?"
/// is a measurement rather than an assumption.
pub trait Normalize {
    /// What [`Normalize::normalize`] reports about the work it did.
    type Receipt;

    /// Reduce to the normal form, returning a receipt describing the work.
    fn normalize(&mut self) -> Self::Receipt;

    /// Whether the value is already in normal form.
    fn is_normalized(&self) -> bool;
}

/// What a [`Normalize::normalize`] call on a rational did.
///
/// Recorded rather than discarded because the whole argument for on-demand
/// normalization is that the gcds are rare; a receipt is how a benchmark
/// finds out whether they are.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalizationReceipt {
    /// The gcd that was divided out (one when the value was already reduced).
    pub common_factor: BigUint,
    /// Bits in the numerator before the reduction.
    pub numerator_bits_before: u64,
    /// Bits in the numerator after the reduction.
    pub numerator_bits_after: u64,
}

/// A univariate polynomial over an exact commutative ring.
///
/// The sketch is a trait rather than a struct because the two concrete
/// carriers — `ZPoly` over [`BigInt`] and `QPoly` over `BigRat` — differ in
/// which operations are cheap, and the migration lanes will land them
/// separately.
pub trait UnivariatePoly: Sized {
    /// The coefficient ring.
    type Coeff;

    /// The degree, or `None` for the zero polynomial.
    fn degree(&self) -> Option<usize>;

    /// The coefficient of `x^index`.
    fn coefficient(&self, index: usize) -> Self::Coeff;

    /// Evaluate at a point of the coefficient ring.
    fn evaluate(&self, at: &Self::Coeff) -> Self::Coeff;

    /// The formal derivative.
    #[must_use]
    fn derivative(&self) -> Self;
}

/// The fraction-free operations that make polynomial gcd over ℤ affordable.
///
/// Working over ℚ and clearing denominators at the end is the implementation
/// six modules in this workspace independently wrote; the coefficient growth
/// that makes it slow is what Collins' reduced PRS and the subresultant PRS
/// exist to bound.
pub trait FractionFree: Sized {
    /// The certificate a gcd carries.
    type GcdCertificate;

    /// The pseudo-remainder `prem(self, divisor)`.
    fn pseudo_remainder(&self, divisor: &Self) -> Option<Self>;

    /// The subresultant polynomial remainder sequence of `self` and `other`.
    fn subresultant_prs(&self, other: &Self) -> Vec<Self>;

    /// The resultant, computed from the subresultant PRS.
    fn resultant(&self, other: &Self) -> Option<Self>;

    /// The primitive gcd, with a certificate the caller can re-derive.
    fn gcd_certified(&self, other: &Self) -> (Self, Self::GcdCertificate);
}

/// Bézout data for an integer gcd: `gcd = cofactor_a·input_a + cofactor_b·input_b`.
///
/// The certificate a caller can re-derive with two multiplications and an
/// addition, which is the standard this crate holds every gcd to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BezoutCertificate {
    /// The claimed gcd.
    pub gcd: BigInt,
    /// The multiplier of `input_a`.
    pub cofactor_a: BigInt,
    /// The multiplier of `input_b`.
    pub cofactor_b: BigInt,
    /// The first input.
    pub input_a: BigInt,
    /// The second input.
    pub input_b: BigInt,
}

impl BezoutCertificate {
    /// Re-derive the Bézout identity and the two divisibility conditions.
    ///
    /// Three independently-failable guards, each with its own forgery test in
    /// [`upoly`]:
    ///
    /// 1. **the sign** — Bézout certifies a gcd only up to sign (design note
    ///    §3.2), so `gcd ≥ 0` is pinned here rather than assumed;
    /// 2. **the identity** `cofactor_a·input_a + cofactor_b·input_b = gcd`;
    /// 3. **divisibility** — `gcd` divides both inputs.
    ///
    /// Guard 2 alone is not a checker: `u·a + v·b` is a multiple of the true
    /// gcd for *any* cofactors, so `6·1 + 4·1 = 10` satisfies it while dividing
    /// neither input. Guard 3 alone is not a checker either: every common
    /// divisor passes it. The pair is what pins the value.
    ///
    /// A zero `gcd` is accepted only when both inputs are zero.
    pub fn verify(&self) -> bool {
        upoly::verify_bezout_certificate(self)
    }
}

/// A Sturm sequence and the root count it claims on an interval.
///
/// `qe_big.rs` and `fps_analytic.rs` each carry their own Sturm chain today.
/// The certificate is what lets the shared one replace both without either
/// lane having to trust it: the sign-variation count is recomputed from the
/// chain, and the chain is recomputed from the polynomial.
#[derive(Debug, Clone)]
pub struct SturmCertificate {
    /// The chain, starting with the polynomial and its derivative, as
    /// little-endian integer coefficient lists.
    pub chain: Vec<Vec<BigInt>>,
    /// The interval's lower endpoint.
    pub lower: BigRational,
    /// The interval's upper endpoint.
    pub upper: BigRational,
    /// The claimed number of distinct real roots in `(lower, upper]`.
    pub root_count: usize,
}

impl SturmCertificate {
    /// Recompute the chain and the sign variations and compare.
    ///
    /// Two *separate* re-derivations, which is the point:
    ///
    /// 1. **the chain** is rebuilt from its own recorded first member by
    ///    [`SturmChain::from_integer_polynomial`] and compared member by
    ///    member. A tampered member is caught here even when it changes no sign
    ///    variation — a positive rescale of one member, say, which guard 2
    ///    cannot see.
    /// 2. **the count** is recomputed as the sign-variation difference of the
    ///    **recorded** chain. A tampered count is caught here even when the
    ///    chain is perfect.
    ///
    /// Plus the three structural conditions: a non-empty chain, a non-zero
    /// first member, and `lower ≤ upper`.
    ///
    /// The chain members are expected in this crate's convention — primitive
    /// integer polynomials reached by a **positive** rational scale, the
    /// convention `fps_analytic.rs` uses. A chain recorded in another
    /// normalization is rejected by guard 1 even if its counts are right, which
    /// is deliberate: the certificate names one chain, not an equivalence class
    /// of them.
    pub fn verify(&self) -> bool {
        upoly::verify_sturm_certificate(self)
    }
}

/// Arithmetic modulo a fixed modulus.
///
/// The design note (§5) describes this trait's intended production
/// implementation as Montgomery form for an odd modulus and Barrett
/// reduction otherwise. [`PlainModRing`], the implementation landed with
/// migration slice 2, does neither: it reduces with `num-bigint`'s native
/// `%` (Knuth Algorithm D underneath, per the design note §3.2's read of
/// `division.rs`). That is a **performance** deviation from the design note,
/// not a correctness one — the trait's public shape, [`PowModCertificate`]'s
/// shape, and the "chain of intermediate residues" semantics are exactly
/// what the design promises, so a later lane can drop in Barrett/Montgomery
/// under the same API without another public-surface change. This slice's
/// migration sites (`ntheory.rs`'s two integer `pow_mod`s) never see a
/// modulus past 128 bits in production, so the plain route was chosen over
/// spending this slice's budget on a second reduction algorithm and a second
/// differential oracle for it.
pub trait ModularRing {
    /// The element type.
    type Element;

    /// The modulus.
    fn modulus(&self) -> &BigUint;

    /// Reduce an integer into the ring.
    fn reduce(&self, value: &BigInt) -> Self::Element;

    /// The product.
    fn mul(&self, lhs: &Self::Element, rhs: &Self::Element) -> Self::Element;

    /// `base^exponent`, with a certificate recording the square-and-multiply
    /// chain so that a checker never has to form `base^exponent` itself.
    ///
    /// ADR-1622 is the reason this is on the trait rather than left to the
    /// caller: a kernel reconstruction that asks for the literal power is
    /// bounded by the largest numeral it forms, and that bound is a modulus
    /// near 101.
    fn pow_mod(&self, base: &Self::Element, exponent: &BigUint) -> PowModCertificate;
}

/// The ring `ℤ / modulus·ℤ`, reduced with plain (schoolbook) division.
///
/// See [`ModularRing`]'s doc comment for why this is "plain" rather than
/// Barrett/Montgomery, and why that is a scoped, documented deviation from
/// the design note rather than a silent one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlainModRing {
    modulus: BigUint,
}

impl PlainModRing {
    /// The ring `ℤ / modulus·ℤ`.
    ///
    /// # Panics
    ///
    /// Panics if `modulus` is zero: there is no such ring, and every caller
    /// in this crate's migration sites already guards against a
    /// non-positive modulus before constructing one (`ntheory.rs`'s
    /// `mod_pow` returns `None` for `modulus <= 0` without ever reaching
    /// here).
    #[must_use]
    pub fn new(modulus: BigUint) -> Self {
        assert!(modulus.bits() != 0, "PlainModRing requires modulus >= 1");
        Self { modulus }
    }
}

impl ModularRing for PlainModRing {
    type Element = BigUint;

    fn modulus(&self) -> &BigUint {
        &self.modulus
    }

    fn reduce(&self, value: &BigInt) -> BigUint {
        let modulus_signed = BigInt::from(self.modulus.clone());
        let mut remainder = value % &modulus_signed;
        if remainder.sign() == Sign::Minus {
            remainder += &modulus_signed;
        }
        remainder
            .to_biguint()
            .expect("a value reduced modulo a positive modulus is non-negative")
    }

    fn mul(&self, lhs: &BigUint, rhs: &BigUint) -> BigUint {
        (lhs * rhs) % &self.modulus
    }

    fn pow_mod(&self, base: &BigUint, exponent: &BigUint) -> PowModCertificate {
        let base_reduced = base % &self.modulus;
        let bit_len = exponent.bits();
        let one = if self.modulus == BigUint::from(1u8) {
            BigUint::from(0u8)
        } else {
            BigUint::from(1u8)
        };
        let mut chain = Vec::with_capacity(usize::try_from(bit_len).unwrap_or(usize::MAX));
        let mut accumulator = one;
        for bit_index in (0..bit_len).rev() {
            accumulator = (&accumulator * &accumulator) % &self.modulus;
            if exponent.bit(bit_index) {
                accumulator = (&accumulator * &base_reduced) % &self.modulus;
            }
            chain.push(accumulator.clone());
        }
        PowModCertificate {
            modulus: self.modulus.clone(),
            base: base_reduced,
            exponent: exponent.clone(),
            residue: accumulator,
            chain,
        }
    }
}

/// The square-and-multiply chain behind one modular exponentiation.
///
/// Each step is a congruence the checker can discharge on its own with one
/// multiplication and one reduction, which is what keeps the largest numeral
/// a reconstruction forms below the modulus rather than at `base^exponent`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PowModCertificate {
    /// The modulus.
    pub modulus: BigUint,
    /// The base.
    pub base: BigUint,
    /// The exponent.
    pub exponent: BigUint,
    /// The claimed residue.
    pub residue: BigUint,
    /// The intermediate residues, one per bit of the exponent, most
    /// significant bit first.
    pub chain: Vec<BigUint>,
}

impl PowModCertificate {
    /// Re-derive the chain step by step, most-significant bit first, and
    /// compare every intermediate residue and the final one.
    ///
    /// Never trusts anything the producer computed: `base` is reduced fresh
    /// from the recorded field, and every squaring/multiply-and-reduce step
    /// is redone from `exponent`'s own bits. Four independently-failable
    /// conditions, in the same spirit as [`RadixCertificate::verify`]:
    ///
    /// 1. the modulus is at least one (there is no ring modulo zero, and
    ///    without this check the reduction below would divide by it);
    /// 2. the chain has exactly one entry per bit of the exponent — a
    ///    chain padded with extra, otherwise-consistent entries is caught
    ///    here rather than by re-deriving a value that happens to still
    ///    match (the case a length-blind check would pass);
    /// 3. recomputing the square-and-multiply chain reproduces every
    ///    recorded intermediate residue, not only the last one; and
    /// 4. the final recomputed residue matches the claimed one.
    #[must_use]
    pub fn verify(&self) -> bool {
        if self.modulus.bits() == 0 {
            return false;
        }
        let bit_len = self.exponent.bits();
        if self.chain.len() as u64 != bit_len {
            return false;
        }
        let base_reduced = &self.base % &self.modulus;
        let one = if self.modulus == BigUint::from(1u8) {
            BigUint::from(0u8)
        } else {
            BigUint::from(1u8)
        };
        let mut accumulator = one;
        for (position, bit_index) in (0..bit_len).rev().enumerate() {
            accumulator = (&accumulator * &accumulator) % &self.modulus;
            if self.exponent.bit(bit_index) {
                accumulator = (&accumulator * &base_reduced) % &self.modulus;
            }
            if self.chain[position] != accumulator {
                return false;
            }
        }
        accumulator == self.residue
    }
}

/// Hensel lifting: a root modulo `p^k` refined to a root modulo `p^(2k)`.
pub trait HenselLift: Sized {
    /// Lift `self`, a solution modulo `prime^precision`, to modulo
    /// `prime^(2·precision)`.
    fn lift(&self, prime: &BigUint, precision: u32) -> Option<Self>;
}

/// A real algebraic number: a defining polynomial plus an isolating interval.
///
/// `axeyum-ir`'s `RealAlgebraic` and `axeyum-cas`'s `real_algebraic` are the
/// two existing carriers. Whether this type lives here or stays in the CAS is
/// the first of the three questions the design note leaves open.
pub trait AlgebraicNumber {
    /// The sign of the number: negative, zero or positive.
    fn sign(&self) -> Ordering;

    /// Refine the isolating interval until it is narrower than `2^-bits`.
    fn refine(&mut self, bits: u64);

    /// A dyadic enclosure of the number at the current refinement.
    fn enclosure(&self) -> (Dyadic, Dyadic);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(value: i64) -> BigInt {
        BigInt::from(value)
    }

    fn nat(value: u64) -> BigUint {
        BigUint::from(value)
    }

    // -- Dyadic ------------------------------------------------------------

    #[test]
    fn a_dyadic_is_normalized_to_an_odd_mantissa() {
        // 12 · 2^0 == 3 · 2^2
        let value = Dyadic::new(big(12), 0).unwrap();
        assert_eq!(value.mantissa(), &big(3));
        assert_eq!(value.exponent(), 2);
        assert_eq!(value, Dyadic::new(big(3), 2).unwrap());
    }

    #[test]
    fn dyadic_zero_has_exponent_zero_whatever_it_was_built_with() {
        assert_eq!(Dyadic::new(big(0), 17).unwrap(), Dyadic::zero());
        assert_eq!(Dyadic::zero().precision_bits(), 0);
    }

    #[test]
    fn dyadic_addition_is_exact_and_normalizes_the_carry() {
        // 1/2 + 1/2 == 1
        let half = Dyadic::new(big(1), -1).unwrap();
        let sum = half.checked_add(&half).unwrap();
        assert_eq!(sum, Dyadic::from_i64(1));
    }

    #[test]
    fn dyadic_subtraction_of_equals_is_zero() {
        let value = Dyadic::new(big(-7), -13).unwrap();
        assert_eq!(value.checked_sub(&value).unwrap(), Dyadic::zero());
    }

    #[test]
    fn dyadic_multiplication_adds_exponents_and_keeps_the_mantissa_odd() {
        let lhs = Dyadic::new(big(3), -2).unwrap();
        let rhs = Dyadic::new(big(5), 7).unwrap();
        let product = lhs.checked_mul(&rhs).unwrap();
        assert_eq!(product.mantissa(), &big(15));
        assert_eq!(product.exponent(), 5);
    }

    #[test]
    fn dyadic_multiplication_declines_rather_than_wrapping_the_exponent() {
        let big_exponent = Dyadic::new(big(1), MAX_EXPONENT).unwrap();
        assert!(big_exponent.checked_mul(&big_exponent).is_none());
    }

    #[test]
    fn dyadic_addition_declines_beyond_the_alignment_budget() {
        let low = Dyadic::new(big(1), -MAX_EXPONENT).unwrap();
        let high = Dyadic::new(big(1), MAX_EXPONENT).unwrap();
        assert!(low.align_cost_bits(&high).is_none());
        assert!(low.checked_add(&high).is_none());
    }

    #[test]
    fn rounding_down_and_up_bracket_the_exact_value() {
        // 11 = 0b1011, four significant bits, rounded to two: the brackets are
        // 0b10_00 = 8 and 0b11_00 = 12.
        let value = Dyadic::new(big(11), 0).unwrap();
        let down = value.round(2, Round::Down).unwrap();
        let up = value.round(2, Round::Up).unwrap();
        assert_eq!(down, Dyadic::from_i64(8));
        assert_eq!(up, Dyadic::from_i64(12));
        assert!(down < value);
        assert!(value < up);
        assert!(down.precision_bits() <= 2);
        assert!(up.precision_bits() <= 2);
    }

    #[test]
    fn rounding_a_negative_value_down_grows_its_magnitude() {
        let value = Dyadic::new(big(-11), 0).unwrap();
        let down = value.round(2, Round::Down).unwrap();
        let toward_zero = value.round(2, Round::TowardZero).unwrap();
        assert_eq!(down, Dyadic::from_i64(-12));
        assert_eq!(toward_zero, Dyadic::from_i64(-8));
        assert!(down < value);
        assert!(value < toward_zero);
        // Down on a negative is the mirror of Up on its magnitude.
        let mirrored = Dyadic::from_i64(11).round(2, Round::Up).unwrap();
        assert_eq!(down.negate(), mirrored);
    }

    #[test]
    fn nearest_ties_to_even_breaks_an_exact_tie_toward_the_even_mantissa() {
        // 11 = 0b1011 to three bits: exactly between 0b101_0 = 10 and
        // 0b110_0 = 12. The mantissa 0b110 is the even one, so 12 wins.
        let eleven = Dyadic::from_i64(11);
        assert_eq!(
            eleven.round(3, Round::NearestTiesToEven).unwrap(),
            Dyadic::from_i64(12)
        );
        // 13 = 0b1101 to three bits: exactly between 0b110_0 = 12 and
        // 0b111_0 = 14. Now 0b110 is the even one, so 12 wins again -- the tie
        // is broken by the mantissa, not by a fixed direction.
        let thirteen = Dyadic::from_i64(13);
        assert_eq!(
            thirteen.round(3, Round::NearestTiesToEven).unwrap(),
            Dyadic::from_i64(12)
        );
    }

    #[test]
    fn a_value_that_already_fits_is_returned_unchanged_by_every_mode() {
        let value = Dyadic::new(big(5), -3).unwrap();
        for mode in [
            Round::Down,
            Round::Up,
            Round::TowardZero,
            Round::AwayFromZero,
            Round::NearestTiesToEven,
        ] {
            assert_eq!(value.round(8, mode).unwrap(), value, "mode {mode:?}");
        }
        assert!(value.round(0, Round::Down).is_none());
    }

    #[test]
    fn rounding_outward_contains_the_input_interval() {
        let lower = Dyadic::new(big(11), -4).unwrap();
        let upper = Dyadic::new(big(13), -4).unwrap();
        let (low, high) = Dyadic::round_outward(&lower, &upper, 2).unwrap();
        assert!(low <= lower);
        assert!(upper <= high);
    }

    #[test]
    fn a_dyadic_converts_to_its_exact_rational() {
        let value = Dyadic::new(big(-3), -2).unwrap();
        assert_eq!(value.to_rational(), BigRational::new(big(-3), big(4)));
        let integral = Dyadic::new(big(5), 3).unwrap();
        assert_eq!(integral.to_rational(), BigRational::from(big(40)));
    }

    #[test]
    fn a_third_rounds_to_the_dyadics_that_bracket_it() {
        let third = BigRational::new(big(1), big(3));
        let down = Dyadic::from_rational(&third, 4, Round::Down).unwrap();
        let up = Dyadic::from_rational(&third, 4, Round::Up).unwrap();
        assert!(down.to_rational() < third);
        assert!(third < up.to_rational());
        assert!(down.precision_bits() <= 4);
        assert!(up.precision_bits() <= 4);
        // 1/3 lands between 10·2^-5 = 5/16 and 11·2^-5, so the gap is one unit
        // in the last place at this exponent: 2^-5.
        assert_eq!(down, Dyadic::new(big(5), -4).unwrap());
        assert_eq!(up, Dyadic::new(big(11), -5).unwrap());
        let gap = up.checked_sub(&down).unwrap();
        assert_eq!(gap, Dyadic::new(big(1), -5).unwrap());
    }

    #[test]
    fn an_exactly_representable_rational_rounds_to_itself_in_every_mode() {
        let three_quarters = BigRational::new(big(3), big(4));
        for mode in [
            Round::Down,
            Round::Up,
            Round::TowardZero,
            Round::AwayFromZero,
            Round::NearestTiesToEven,
        ] {
            let rounded = Dyadic::from_rational(&three_quarters, 8, mode).unwrap();
            assert_eq!(rounded.to_rational(), three_quarters, "mode {mode:?}");
        }
    }

    #[test]
    fn from_rational_rounds_a_negative_in_the_named_direction() {
        let value = BigRational::new(big(-1), big(3));
        let down = Dyadic::from_rational(&value, 4, Round::Down).unwrap();
        let up = Dyadic::from_rational(&value, 4, Round::Up).unwrap();
        assert!(down.to_rational() < value);
        assert!(value < up.to_rational());
    }

    #[test]
    fn dyadic_ordering_agrees_with_the_rational_ordering() {
        let mut values = [
            Dyadic::new(big(-3), -1).unwrap(),
            Dyadic::new(big(1), -8).unwrap(),
            Dyadic::zero(),
            Dyadic::new(big(5), 2).unwrap(),
            Dyadic::new(big(1), 0).unwrap(),
        ];
        values.sort_unstable();
        for pair in values.windows(2) {
            assert!(pair[0].to_rational() <= pair[1].to_rational());
        }
    }

    // -- Radix -------------------------------------------------------------

    #[test]
    fn a_radix_below_two_is_refused() {
        assert!(Radix::new(nat(0)).is_none());
        assert!(Radix::new(nat(1)).is_none());
        assert!(Radix::new(nat(2)).is_some());
    }

    #[test]
    fn base_ten_expansion_has_the_digits_you_would_write_down() {
        let radix = Radix::new(nat(10)).unwrap();
        let certificate = radix.expand(&nat(2_147_483_647));
        // Little-endian.
        let digits: Vec<u32> = certificate
            .digits()
            .iter()
            .map(|digit| u32::try_from(digit.clone()).unwrap())
            .collect();
        assert_eq!(digits, vec![7, 4, 6, 3, 8, 4, 7, 4, 1, 2]);
        assert!(certificate.verify());
    }

    #[test]
    fn zero_expands_to_no_digits_and_still_verifies() {
        let radix = Radix::new(nat(7)).unwrap();
        let certificate = radix.expand(&nat(0));
        assert!(certificate.digits().is_empty());
        assert!(certificate.verify());
    }

    #[test]
    fn a_big_base_expansion_verifies_too() {
        // Base 2^32; the kernel bridge's limb chain shape.
        let base = BigUint::from(1u8) << 32u8;
        let radix = Radix::new(base).unwrap();
        let value = (BigUint::from(1u8) << 100u8) + nat(12_345);
        let certificate = radix.expand(&value);
        assert_eq!(certificate.digits().len(), 4);
        assert!(certificate.verify());
    }

    #[test]
    fn evaluate_refuses_a_digit_that_is_not_below_the_base() {
        let radix = Radix::new(nat(10)).unwrap();
        assert_eq!(radix.evaluate(&[nat(3), nat(4)]), Some(nat(43)));
        assert!(radix.evaluate(&[nat(10)]).is_none());
    }

    #[test]
    fn forged_radix_certificates_all_fail_verification() {
        let radix = Radix::new(nat(10)).unwrap();
        let honest = radix.expand(&nat(4_096));
        assert!(honest.verify());

        // 1. A tampered digit.
        let mut digits = honest.digits().to_vec();
        digits[0] = nat(7);
        let forged = RadixCertificate::from_parts(nat(10), digits, honest.value().clone());
        assert!(!forged.verify(), "a tampered digit must be caught");

        // 2. A tampered value.
        let forged = RadixCertificate::from_parts(nat(10), honest.digits().to_vec(), nat(4_097));
        assert!(!forged.verify(), "a tampered value must be caught");

        // 3. A non-canonical expansion: a zero in the most significant place.
        let mut digits = honest.digits().to_vec();
        digits.push(nat(0));
        let forged = RadixCertificate::from_parts(nat(10), digits, honest.value().clone());
        assert!(!forged.verify(), "a leading zero digit must be caught");

        // 4. A digit that is not below the base, arranged so that Horner
        //    evaluation still reproduces the value -- the case a value-only
        //    check would pass. 40 = 4*10 + 0 = 0*10 + 40.
        let forged = RadixCertificate::from_parts(nat(10), vec![nat(40)], nat(40));
        assert!(
            !forged.verify(),
            "an out-of-range digit must be caught even when the value re-derives"
        );

        // 5. A base below two.
        let forged = RadixCertificate::from_parts(nat(1), vec![nat(0)], nat(0));
        assert!(!forged.verify(), "a base below two must be caught");
    }

    #[test]
    fn mixed_radix_expands_and_verifies() {
        let system = MixedRadix::new(vec![nat(3), nat(5), nat(7)]).unwrap();
        assert_eq!(system.modulus(), nat(105));
        let certificate = system.expand(&nat(100)).unwrap();
        // 100 = 1 + 3*(3 + 5*6) -> digits [1, 3, 6]
        let digits: Vec<u64> = certificate
            .digits()
            .iter()
            .map(|digit| u64::try_from(digit.clone()).unwrap())
            .collect();
        assert_eq!(digits, vec![1, 3, 6]);
        assert!(certificate.verify());
        assert!(system.expand(&nat(105)).is_none());
    }

    #[test]
    fn forged_mixed_radix_certificates_fail_verification() {
        let system = MixedRadix::new(vec![nat(3), nat(5), nat(7)]).unwrap();
        let honest = system.expand(&nat(100)).unwrap();

        let mut digits = honest.digits().to_vec();
        digits[1] = nat(4);
        let forged = MixedRadixCertificate::from_parts(
            honest.bases().to_vec(),
            digits,
            honest.value().clone(),
        );
        assert!(!forged.verify(), "a tampered digit must be caught");

        // A digit at or above its own base, with the value made to match.
        let forged = MixedRadixCertificate::from_parts(
            vec![nat(3), nat(5), nat(7)],
            vec![nat(5), nat(0), nat(0)],
            nat(5),
        );
        assert!(!forged.verify(), "an out-of-range digit must be caught");

        // A digit list that does not match the base list.
        let forged =
            MixedRadixCertificate::from_parts(vec![nat(3), nat(5), nat(7)], vec![nat(1)], nat(1));
        assert!(!forged.verify(), "a length mismatch must be caught");
    }

    // -- ModularRing / PowModCertificate ------------------------------------

    /// A wholly independent reference `pow_mod`: ordinary left-to-right
    /// square-and-multiply written directly against `BigUint`'s own `%` and
    /// `*`, sharing no code path with [`PlainModRing::pow_mod`]. This is the
    /// oracle the differential test below checks the ring against.
    fn naive_pow_mod(base: &BigUint, exponent: &BigUint, modulus: &BigUint) -> BigUint {
        if *modulus == BigUint::from(1u8) {
            return BigUint::from(0u8);
        }
        let mut result = BigUint::from(1u8);
        let mut factor = base % modulus;
        let mut remaining = exponent.clone();
        let two = BigUint::from(2u8);
        while remaining.bits() != 0 {
            if remaining.bit(0) {
                result = (&result * &factor) % modulus;
            }
            factor = (&factor * &factor) % modulus;
            remaining /= &two;
        }
        result
    }

    #[test]
    fn plain_mod_ring_matches_a_naive_reference_including_moduli_past_u128() {
        let cases: Vec<(BigUint, BigUint, BigUint)> = vec![
            // Small, hand-checkable.
            (nat(2), nat(10), nat(1_000)),
            (nat(3), nat(0), nat(5)),
            (nat(0), nat(0), nat(1)),
            (nat(7), nat(1), nat(1)),
            (nat(4), nat(13), nat(497)),
            // Even and odd moduli.
            (nat(5), nat(117), nat(190)),
            (nat(5), nat(117), nat(191)),
            // A modulus past `u128::MAX`, exercised only because this crate's
            // whole reason to exist is the arithmetic `u128` cannot do.
            (
                BigUint::from(2u8).pow(200) + BigUint::from(7u8),
                BigUint::from(2u8).pow(129) - BigUint::from(1u8),
                BigUint::from(2u8).pow(256) - BigUint::from(189u16),
            ),
            (
                BigUint::from(3u8),
                BigUint::from(2u8).pow(300),
                BigUint::from(2u8).pow(257) + BigUint::from(1u8),
            ),
        ];
        for (base, exponent, modulus) in cases {
            let ring = PlainModRing::new(modulus.clone());
            let certificate = ring.pow_mod(&base, &exponent);
            assert!(
                certificate.verify(),
                "certificate for base={base} exponent={exponent} modulus={modulus} must verify"
            );
            let expected = naive_pow_mod(&base, &exponent, &modulus);
            assert_eq!(
                certificate.residue, expected,
                "base={base} exponent={exponent} modulus={modulus}"
            );
        }
    }

    #[test]
    fn pow_mod_certificate_chain_has_one_entry_per_exponent_bit() {
        let ring = PlainModRing::new(nat(1_000_003));
        let certificate = ring.pow_mod(&nat(2), &nat(999_999));
        assert_eq!(certificate.chain.len() as u64, nat(999_999).bits());
        assert_eq!(certificate.chain.last(), Some(&certificate.residue));

        // Exponent zero: an empty chain, residue `1 mod modulus`.
        let zero_exp = ring.pow_mod(&nat(5), &nat(0));
        assert!(zero_exp.chain.is_empty());
        assert_eq!(zero_exp.residue, nat(1));
        assert!(zero_exp.verify());
    }

    #[test]
    #[should_panic(expected = "PlainModRing requires modulus >= 1")]
    fn plain_mod_ring_rejects_a_zero_modulus() {
        let _ = PlainModRing::new(nat(0));
    }

    #[test]
    fn forged_pow_mod_certificates_all_fail_verification() {
        let ring = PlainModRing::new(nat(1_000_003));
        let honest = ring.pow_mod(&nat(2), &nat(999_999));
        assert!(honest.verify());

        // 1. A zero modulus: there is no such ring, and without this guard
        //    the reduction below would divide by it.
        let forged = PowModCertificate {
            modulus: nat(0),
            base: nat(0),
            exponent: nat(0),
            residue: nat(0),
            chain: Vec::new(),
        };
        assert!(!forged.verify(), "a zero modulus must be caught");

        // 2. A chain padded with one extra, otherwise-consistent entry --
        //    the case a length-blind check would pass.
        let mut chain = honest.chain.clone();
        chain.push(honest.residue.clone());
        let forged = PowModCertificate {
            chain,
            ..honest.clone()
        };
        assert!(!forged.verify(), "a padded chain must be caught");

        // 3. A tampered intermediate residue, with the final `residue` field
        //    left at the true (correct) value.
        let mut chain = honest.chain.clone();
        let mid = chain.len() / 2;
        chain[mid] = chain[mid].clone() + BigUint::from(1u8);
        let forged = PowModCertificate {
            chain,
            ..honest.clone()
        };
        assert!(
            !forged.verify(),
            "a tampered intermediate residue must be caught"
        );

        // 4. A tampered final residue, with every chain entry left correct.
        let forged = PowModCertificate {
            residue: honest.residue.clone() + BigUint::from(1u8),
            ..honest.clone()
        };
        assert!(!forged.verify(), "a tampered final residue must be caught");
    }
}
