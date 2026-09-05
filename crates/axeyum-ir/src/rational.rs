//! Exact rational numbers for linear real arithmetic (ADR-0015, ADR-1702).
//!
//! A [`Rational`] is a normalized fraction: the denominator is always positive,
//! the fraction is in lowest terms, and zero is `0/1`. Normalization makes the
//! representation canonical, so structural `Eq`/`Hash` coincide with value
//! equality and the type can key the term interner.
//!
//! # Two representations, one value
//!
//! Per **ADR-1702** the type is an `i128` **fast path** with an
//! arbitrary-precision **slow path**:
//!
//! - **small** — `num`/`den` are the `i128` fraction directly, `den > 0`.
//! - **big** — the value did not fit `i128`, so it lives in a process-global
//!   deduplicating pool and `num` holds its pool id, marked by `den == 0`
//!   (impossible for a small, whose denominator is always positive).
//!
//! `i128` overflow **promotes** to the big path rather than declining, and any
//! result that fits `i128` again is **demoted** back, so the fast path is
//! retaken after transient growth. Because promotion happens only for values
//! that genuinely do not fit and every fitting result is demoted, **each value
//! has exactly one representation** — which is what keeps derived `Eq` (and the
//! `TermNode` interner that depends on it) correct.
//!
//! The struct is still two `i128` fields, so it stays `Copy` and its size and
//! layout are unchanged; that matters because `Rational` is consumed by value in
//! thousands of places and is a field of the interned `TermNode::RealConst`.
//!
//! # Soundness
//!
//! Both paths compute the same mathematical value — `BigRational` normalizes to
//! the same canonical form and the demotion check (`BigInt::to_i128`) is exact —
//! so no verdict built on this type can change. Only an `unknown` caused by
//! running out of range can become a decision. The pool id is never observable:
//! `Eq`, `Ord`, `Hash` and `Display` are all defined on the value, so a run that
//! assigns different ids still produces identical output.
//!
//! # The one hazard
//!
//! [`Rational::numerator`] and [`Rational::denominator`] return `i128` and
//! therefore **panic** on a value outside that range. Saturating would turn an
//! out-of-range value into a silently wrong one, which this project does not
//! accept. Use [`Rational::checked_numerator`] / [`Rational::numerator_big`]
//! (and the `denominator` counterparts) on any route that must not panic.

use std::sync::{LazyLock, RwLock};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;

use crate::fast_map::FastMap;

/// Maximum number of **distinct** out-of-`i128` rational values one process will
/// intern (ADR-1702).
///
/// The pool is append-only — `Rational` is `Copy`, so there is no `Drop` to hang
/// reclamation on — and this cap is what stops that from turning a fast
/// `unknown` into an out-of-memory. Past it, promotion fails and every operation
/// behaves exactly as it did before ADR-1702: the `checked_*` family returns
/// `None` and the operators panic.
const BIG_POOL_CAPACITY: usize = 1 << 20;

/// The process-global pool of promoted rationals, deduplicated by value so a
/// pool id determines the value and vice versa.
struct BigPool {
    values: Vec<BigRational>,
    index: FastMap<BigRational, u32>,
}

static BIG_POOL: LazyLock<RwLock<BigPool>> = LazyLock::new(|| {
    RwLock::new(BigPool {
        values: Vec::new(),
        index: FastMap::default(),
    })
});

/// Interns `value`, returning its pool id, or `None` if the pool is at capacity.
fn intern_big(value: &BigRational) -> Option<u32> {
    {
        let pool = BIG_POOL
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(id) = pool.index.get(value) {
            return Some(*id);
        }
    }
    let mut pool = BIG_POOL
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    // Re-check under the write lock: another thread may have interned it.
    if let Some(id) = pool.index.get(value) {
        return Some(*id);
    }
    if pool.values.len() >= BIG_POOL_CAPACITY {
        return None;
    }
    let id = u32::try_from(pool.values.len()).ok()?;
    pool.values.push(value.clone());
    pool.index.insert(value.clone(), id);
    Some(id)
}

/// The pooled value for `id`. Ids are only ever produced by [`intern_big`], and
/// the pool never shrinks, so this cannot be out of bounds.
fn pooled(id: u32) -> BigRational {
    let pool = BIG_POOL
        .read()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    pool.values[id as usize].clone()
}

/// An exact rational number `num/den` in lowest terms with `den > 0`.
///
/// See the module documentation for the two-representation design (ADR-1702).
/// Derived `PartialEq`/`Eq` is field equality, which is value equality because
/// the representation is canonical: a value that fits `i128` is always small,
/// and the big pool is deduplicated.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Rational {
    /// Small: the numerator (sign lives here). Big: the pool id.
    num: i128,
    /// Small: the denominator, always `> 0`. Big: exactly `0`.
    den: i128,
}

impl Default for Rational {
    /// The default rational is zero.
    fn default() -> Self {
        Self::zero()
    }
}

/// Normalizes `num/den` entirely within `i128`, or `None` if it does not fit.
///
/// `den` must be non-zero; the caller checks that (a zero denominator is a usage
/// error, not an overflow).
fn small_new(num: i128, den: i128) -> Option<Rational> {
    let mut num = num;
    let mut den = den;
    if den < 0 {
        // Move the sign to the numerator (den stays positive). `checked_neg`
        // guards i128::MIN.
        num = num.checked_neg()?;
        den = den.checked_neg()?;
    }
    let g = gcd(num.unsigned_abs(), den.unsigned_abs());
    if g > 1 {
        // g divides both exactly; the casts are exact (g <= |num|,|den|).
        #[allow(clippy::cast_possible_wrap)]
        let g = g as i128;
        num /= g;
        den /= g;
    }
    Some(Rational { num, den })
}

/// Adds two **small** fractions over the least common denominator, or `None` on
/// `i128` overflow. See [`Rational::checked_add`] for why the LCM form matters.
fn small_add(a: i128, b: i128, c: i128, d: i128) -> Option<Rational> {
    // Both operands are in lowest terms with positive denominators.
    let g = gcd(b.unsigned_abs(), d.unsigned_abs());
    #[allow(clippy::cast_possible_wrap)]
    let g = g as i128;
    // g divides both denominators exactly and g >= 1.
    let b1 = b / g;
    let d1 = d / g;
    let ad = a.checked_mul(d1)?;
    let cb = c.checked_mul(b1)?;
    let num = ad.checked_add(cb)?;
    // The least common denominator: b1 * d == lcm(b, d).
    let den = b1.checked_mul(d)?;
    small_new(num, den)
}

/// Multiplies two **small** fractions with cross-cancellation, or `None` on
/// `i128` overflow. See [`Rational::checked_mul`].
fn small_mul(a: i128, b: i128, c: i128, d: i128) -> Option<Rational> {
    let negative = (a < 0) != (c < 0);
    let mut a = a.unsigned_abs();
    let mut b = b.unsigned_abs();
    let mut c = c.unsigned_abs();
    let mut d = d.unsigned_abs();
    let g1 = gcd(a, d);
    if g1 > 1 {
        a /= g1;
        d /= g1;
    }
    let g2 = gcd(c, b);
    if g2 > 1 {
        c /= g2;
        b /= g2;
    }
    // Both operands were in lowest terms, so after cross-cancellation the
    // product is too — but `small_new` still canonicalizes the zero case.
    let num = a.checked_mul(c)?;
    let den = b.checked_mul(d)?;
    let num = i128::try_from(num).ok()?;
    let den = i128::try_from(den).ok()?;
    small_new(if negative { num.checked_neg()? } else { num }, den)
}

/// Compares two **small** fractions, or `None` on `i128` overflow.
fn small_cmp(a: i128, b: i128, c: i128, d: i128) -> Option<core::cmp::Ordering> {
    // Cheap exact shortcuts that never multiply.
    if b == d {
        return Some(a.cmp(&c));
    }
    if (a < 0) != (c < 0) {
        return Some(a.cmp(&c));
    }
    // Compare over the least common denominator (both denominators are
    // positive, so the direction is preserved).
    let g = gcd(b.unsigned_abs(), d.unsigned_abs());
    #[allow(clippy::cast_possible_wrap)]
    let g = g as i128;
    let lhs = a.checked_mul(d / g)?;
    let rhs = c.checked_mul(b / g)?;
    Some(lhs.cmp(&rhs))
}

impl Rational {
    /// `true` if this value is stored on the `i128` fast path.
    #[inline]
    const fn is_small(self) -> bool {
        self.den > 0
    }

    /// The pool id of a promoted value, or `None` if this is a small value.
    fn big_id(self) -> Option<u32> {
        if self.den == 0 {
            Some(u32::try_from(self.num).expect("big-rational pool id fits u32"))
        } else {
            None
        }
    }

    /// Wraps a pool id as a big rational.
    fn from_id(id: u32) -> Self {
        Self {
            num: i128::from(id),
            den: 0,
        }
    }

    /// Builds a `Rational` from an arbitrary-precision value, demoting to the
    /// `i128` fast path whenever it fits.
    ///
    /// Returns `None` only if the value needs the pool and the pool is at
    /// capacity ([`Rational::big_pool_capacity`]).
    fn from_big(value: &BigRational) -> Option<Self> {
        if let (Some(num), Some(den)) = (value.numer().to_i128(), value.denom().to_i128()) {
            // `BigRational` is normalized: lowest terms with a positive
            // denominator, exactly the small invariant.
            debug_assert!(den > 0, "BigRational denominator must be positive");
            return Some(Self { num, den });
        }
        intern_big(value).map(Self::from_id)
    }

    /// Creates `num/den` normalized to lowest terms with a positive denominator.
    ///
    /// Since ADR-1702 this does **not** panic on `i128` overflow; the value is
    /// promoted to the arbitrary-precision path instead.
    ///
    /// # Panics
    ///
    /// Panics if `den` is zero, or if the value needs the big-rational pool and
    /// the pool is at capacity.
    pub fn new(num: i128, den: i128) -> Self {
        assert!(den != 0, "rational denominator must be non-zero");
        if let Some(small) = small_new(num, den) {
            return small;
        }
        Self::from_big(&BigRational::new(BigInt::from(num), BigInt::from(den)))
            .expect("big-rational pool exhausted")
    }

    /// Creates `num/den` normalized to lowest terms, returning `None` instead of
    /// panicking when the value cannot be represented (`den` zero is a usage
    /// error and still panics).
    ///
    /// **Since ADR-1702 this returns `Some` on the promoted path**: `i128`
    /// overflow during normalization is no longer a failure, so the only `None`
    /// is a big-rational pool at capacity.
    ///
    /// # Panics
    ///
    /// Panics if `den` is zero (a denominator-zero rational is a usage error,
    /// not an overflow).
    #[must_use]
    pub fn checked_new(num: i128, den: i128) -> Option<Self> {
        assert!(den != 0, "rational denominator must be non-zero");
        if let Some(small) = small_new(num, den) {
            return Some(small);
        }
        Self::from_big(&BigRational::new(BigInt::from(num), BigInt::from(den)))
    }

    /// The integer `n` as `n/1`.
    pub fn integer(n: i128) -> Self {
        Self { num: n, den: 1 }
    }

    /// Zero (`0/1`).
    pub fn zero() -> Self {
        Self { num: 0, den: 1 }
    }

    /// `true` if this value is outside the `i128` fast path (ADR-1702).
    ///
    /// Only [`Rational::numerator`] and [`Rational::denominator`] behave
    /// differently for such a value — they panic rather than truncate.
    #[inline]
    #[must_use]
    pub const fn is_big(self) -> bool {
        self.den == 0
    }

    /// The numerator (sign lives here).
    ///
    /// # Panics
    ///
    /// Panics if the numerator does not fit `i128` (see [`Rational::is_big`]).
    /// Use [`Rational::checked_numerator`] or [`Rational::numerator_big`] on a
    /// route that must not panic.
    #[inline]
    pub fn numerator(self) -> i128 {
        if self.is_small() {
            return self.num;
        }
        self.checked_numerator()
            .expect("rational numerator exceeds i128; use checked_numerator() or numerator_big()")
    }

    /// The denominator (always positive).
    ///
    /// # Panics
    ///
    /// Panics if the denominator does not fit `i128`. Note that a promoted value
    /// may still have a small denominator (a huge integer is `n/1`), so this can
    /// succeed where [`Rational::numerator`] panics.
    #[inline]
    pub fn denominator(self) -> i128 {
        if self.is_small() {
            return self.den;
        }
        self.checked_denominator().expect(
            "rational denominator exceeds i128; use checked_denominator() or denominator_big()",
        )
    }

    /// The numerator if it fits `i128`, else `None`. Never panics.
    #[inline]
    #[must_use]
    pub fn checked_numerator(self) -> Option<i128> {
        if self.is_small() {
            return Some(self.num);
        }
        self.to_big_rational().numer().to_i128()
    }

    /// The denominator if it fits `i128`, else `None`. Never panics.
    #[inline]
    #[must_use]
    pub fn checked_denominator(self) -> Option<i128> {
        if self.is_small() {
            return Some(self.den);
        }
        self.to_big_rational().denom().to_i128()
    }

    /// The numerator at arbitrary precision.
    #[must_use]
    pub fn numerator_big(self) -> BigInt {
        if self.is_small() {
            return BigInt::from(self.num);
        }
        self.to_big_rational().numer().clone()
    }

    /// The denominator at arbitrary precision (always positive).
    #[must_use]
    pub fn denominator_big(self) -> BigInt {
        if self.is_small() {
            return BigInt::from(self.den);
        }
        self.to_big_rational().denom().clone()
    }

    /// This value as an arbitrary-precision rational.
    #[must_use]
    pub fn to_big_rational(self) -> BigRational {
        match self.big_id() {
            Some(id) => pooled(id),
            // Already in lowest terms with a positive denominator, so the
            // normalizing constructor would only redo work.
            None => BigRational::new_raw(BigInt::from(self.num), BigInt::from(self.den)),
        }
    }

    /// Builds a `Rational` from an arbitrary-precision value (ADR-1702's entry
    /// point for the wide-literal routes), demoting to the `i128` fast path
    /// whenever it fits.
    ///
    /// Returns `None` only if the value needs the pool and the pool is at
    /// capacity ([`Rational::big_pool_capacity`]).
    #[must_use]
    pub fn from_big_rational(value: &BigRational) -> Option<Self> {
        Self::from_big(value)
    }

    /// Number of distinct promoted values this process has interned.
    ///
    /// Observability for the append-only pool; not a value-level property.
    #[must_use]
    pub fn big_pool_len() -> usize {
        let pool = BIG_POOL
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        pool.values.len()
    }

    /// The cap on [`Rational::big_pool_len`]; past it, promotion fails and this
    /// type behaves exactly as it did before ADR-1702.
    #[must_use]
    pub const fn big_pool_capacity() -> usize {
        BIG_POOL_CAPACITY
    }

    /// Returns `true` if this is an integer (denominator one).
    pub fn is_integer(self) -> bool {
        if self.is_small() {
            return self.den == 1;
        }
        self.to_big_rational().is_integer()
    }

    /// Returns `true` if this is zero.
    ///
    /// A promoted value is never zero: zero fits `i128`, so it is always small.
    pub fn is_zero(self) -> bool {
        self.is_small() && self.num == 0
    }

    /// The multiplicative inverse `den/num`.
    ///
    /// # Panics
    ///
    /// Panics if this is zero, or if the big-rational pool is at capacity.
    #[must_use]
    pub fn recip(self) -> Self {
        assert!(!self.is_zero(), "reciprocal of zero rational");
        if self.is_small()
            && let Some(small) = small_new(self.den, self.num)
        {
            return small;
        }
        Self::from_big(&self.to_big_rational().recip()).expect("big-rational pool exhausted")
    }

    /// Exact negation.
    ///
    /// **Since ADR-1702 this returns `Some` on the promoted path**: `i128`
    /// overflow (`num == i128::MIN`) promotes instead of failing, so the only
    /// `None` is a big-rational pool at capacity.
    #[must_use]
    pub fn checked_neg(self) -> Option<Self> {
        if self.is_small()
            && let Some(num) = self.num.checked_neg()
        {
            return Some(Self { num, den: self.den });
        }
        Self::from_big(&-self.to_big_rational())
    }

    /// Exact addition.
    ///
    /// **Since ADR-1702 this returns `Some` on the promoted path**: `i128`
    /// overflow promotes to arbitrary precision instead of failing, so the only
    /// `None` is a big-rational pool at capacity.
    ///
    /// The `i128` fast path adds over the **least** common denominator rather
    /// than the product one: with `g = gcd(b, d)`,
    /// `a/b + c/d = (a·(d/g) + c·(b/g)) / ((b/g)·d)`. The naive
    /// `(a·d + c·b)/(b·d)` leaves the fast path on intermediates whose reduced
    /// result fits comfortably, which is worth avoiding even now that leaving it
    /// costs a promotion rather than an `unknown`.
    #[inline]
    #[must_use]
    pub fn checked_add(self, other: Self) -> Option<Self> {
        if self.is_small()
            && other.is_small()
            && let Some(small) = small_add(self.num, self.den, other.num, other.den)
        {
            return Some(small);
        }
        Self::from_big(&(self.to_big_rational() + other.to_big_rational()))
    }

    /// Exact subtraction.
    ///
    /// **Since ADR-1702 this returns `Some` on the promoted path**; the only
    /// `None` is a big-rational pool at capacity.
    #[inline]
    #[must_use]
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        if self.is_small()
            && other.is_small()
            && let Some(neg) = other.num.checked_neg()
            && let Some(small) = small_add(self.num, self.den, neg, other.den)
        {
            return Some(small);
        }
        Self::from_big(&(self.to_big_rational() - other.to_big_rational()))
    }

    /// Exact multiplication.
    ///
    /// **Since ADR-1702 this returns `Some` on the promoted path**; the only
    /// `None` is a big-rational pool at capacity.
    ///
    /// The `i128` fast path **cross-cancels before multiplying** — `gcd(a, d)`
    /// and `gcd(c, b)` are divided out of `(a/b)·(c/d)` first — so only the
    /// *reduced* product has to fit for the fast path to be kept.
    #[inline]
    #[must_use]
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        if self.is_small()
            && other.is_small()
            && let Some(small) = small_mul(self.num, self.den, other.num, other.den)
        {
            return Some(small);
        }
        Self::from_big(&(self.to_big_rational() * other.to_big_rational()))
    }

    /// Exact division, returning `None` on division by zero.
    ///
    /// **Since ADR-1702 an out-of-range quotient returns `Some`** on the
    /// promoted path; the remaining `None`s are division by zero and a
    /// big-rational pool at capacity.
    #[inline]
    #[must_use]
    pub fn checked_div(self, other: Self) -> Option<Self> {
        if other.is_zero() {
            return None;
        }
        // The reciprocal must be normalized first: `small_mul` assumes both
        // operands are in lowest terms with a POSITIVE denominator, and
        // `(other.den, other.num)` is not when `other` is negative.
        if self.is_small()
            && other.is_small()
            && let Some(recip) = small_new(other.den, other.num)
            && let Some(small) = small_mul(self.num, self.den, recip.num, recip.den)
        {
            return Some(small);
        }
        Self::from_big(&(self.to_big_rational() / other.to_big_rational()))
    }

    /// Total ordering.
    ///
    /// **Since ADR-1702 this always returns `Some`**: a cross-multiplication that
    /// leaves `i128` range falls back to arbitrary-precision comparison, which
    /// allocates no pool entry and therefore cannot fail. The `Option` is kept so
    /// the ~5,500 existing call sites compile unchanged.
    #[inline]
    #[must_use]
    pub fn checked_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        if self.is_small()
            && other.is_small()
            && let Some(ordering) = small_cmp(self.num, self.den, other.num, other.den)
        {
            return Some(ordering);
        }
        Some(self.to_big_rational().cmp(&other.to_big_rational()))
    }
}

impl core::ops::Div for Rational {
    type Output = Self;

    /// Exact division.
    ///
    /// # Panics
    ///
    /// Panics on division by zero, or if the big-rational pool is at capacity.
    #[allow(clippy::suspicious_arithmetic_impl)] // division is multiply-by-reciprocal
    fn div(self, other: Self) -> Self {
        self.checked_div(other).expect("rational division")
    }
}

impl core::ops::Neg for Rational {
    type Output = Self;

    /// Exact negation.
    ///
    /// # Panics
    ///
    /// Panics if the big-rational pool is at capacity.
    fn neg(self) -> Self {
        self.checked_neg().expect("rational negation")
    }
}

impl core::ops::Add for Rational {
    type Output = Self;

    /// Exact addition.
    ///
    /// # Panics
    ///
    /// Panics if the big-rational pool is at capacity.
    fn add(self, other: Self) -> Self {
        self.checked_add(other).expect("rational add")
    }
}

impl core::ops::Sub for Rational {
    type Output = Self;

    /// Exact subtraction.
    ///
    /// # Panics
    ///
    /// Panics if the big-rational pool is at capacity.
    fn sub(self, other: Self) -> Self {
        self.checked_sub(other).expect("rational sub")
    }
}

impl core::ops::Mul for Rational {
    type Output = Self;

    /// Exact multiplication.
    ///
    /// # Panics
    ///
    /// Panics if the big-rational pool is at capacity.
    fn mul(self, other: Self) -> Self {
        self.checked_mul(other).expect("rational mul")
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        if self.is_small()
            && other.is_small()
            && let Some(ordering) = small_cmp(self.num, self.den, other.num, other.den)
        {
            return ordering;
        }
        self.to_big_rational().cmp(&other.to_big_rational())
    }
}

impl core::hash::Hash for Rational {
    /// Hashes the **value**, never the pool id, so the hash of a promoted value
    /// is identical across runs (determinism is a public API promise) and
    /// consistent with the derived field equality.
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        if self.is_small() {
            state.write_u8(0);
            self.num.hash(state);
            self.den.hash(state);
        } else {
            state.write_u8(1);
            self.to_big_rational().hash(state);
        }
    }
}

impl core::fmt::Display for Rational {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_small() {
            return if self.den == 1 {
                write!(f, "{}", self.num)
            } else {
                write!(f, "{}/{}", self.num, self.den)
            };
        }
        let value = self.to_big_rational();
        if value.is_integer() {
            write!(f, "{}", value.numer())
        } else {
            write!(f, "{}/{}", value.numer(), value.denom())
        }
    }
}

impl core::fmt::Debug for Rational {
    /// Prints the value, not the representation — a raw pool id would be
    /// meaningless in a test failure.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_small() {
            write!(f, "Rational({}/{})", self.num, self.den)
        } else {
            let value = self.to_big_rational();
            write!(f, "Rational(big {}/{})", value.numer(), value.denom())
        }
    }
}

/// Greatest common divisor of two unsigned magnitudes (Euclid).
fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::Rational;
    use core::hash::{Hash, Hasher};
    use num_bigint::BigInt;
    use num_rational::BigRational;

    /// `10^exp` built independently of anything under test.
    fn ten_pow(exp: u32) -> BigInt {
        let mut value = BigInt::from(1u32);
        for _ in 0..exp {
            value *= 10u32;
        }
        value
    }

    fn hash_of(value: Rational) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn normalizes_sign_and_lowest_terms() {
        let r = Rational::new(2, -4);
        assert_eq!(r.numerator(), -1);
        assert_eq!(r.denominator(), 2);
        assert_eq!(Rational::new(6, 3), Rational::integer(2));
        assert_eq!(Rational::new(0, 5), Rational::zero());
    }

    #[test]
    fn arithmetic_is_exact() {
        let third = Rational::new(1, 3);
        let sixth = Rational::new(1, 6);
        assert_eq!(third + sixth, Rational::new(1, 2));
        assert_eq!(third - sixth, Rational::new(1, 6));
        assert_eq!(third * Rational::new(3, 1), Rational::integer(1));
        assert_eq!(-third, Rational::new(-1, 3));
    }

    #[test]
    fn ordering_uses_cross_multiplication() {
        assert!(Rational::new(1, 3) < Rational::new(1, 2));
        assert!(Rational::new(-1, 2) < Rational::zero());
        assert_eq!(Rational::new(2, 4), Rational::new(1, 2));
        assert!(Rational::new(5, 3) > Rational::integer(1));
    }

    // --- ADR-1702: promotion, demotion, and representation independence ---

    #[test]
    fn product_across_2_127_promotes_and_is_exact() {
        // 2^100 * 2^100 = 2^200, well past i128::MAX (< 2^127).
        let two_100 = Rational::integer(1i128 << 100);
        let product = two_100 * two_100;
        assert!(product.is_big(), "2^200 must leave the i128 fast path");
        assert!(!two_100.is_big(), "2^100 fits i128 and must stay small");
        let two_200 = BigInt::from(1u32) << 200u32;
        assert_eq!(
            product.to_big_rational(),
            BigRational::new(two_200.clone(), BigInt::from(1u32))
        );
        assert_eq!(product.numerator_big(), two_200);
        assert!(product.is_integer());
        assert_eq!(product.checked_numerator(), None);
        assert_eq!(product.checked_denominator(), Some(1));
        assert_eq!(product.denominator(), 1);
    }

    #[test]
    #[should_panic(expected = "rational numerator exceeds i128")]
    fn numerator_panics_on_a_promoted_value() {
        let two_100 = Rational::integer(1i128 << 100);
        let _ = (two_100 * two_100).numerator();
    }

    #[test]
    fn just_below_and_just_above_the_i128_ceiling() {
        // i128::MAX is not a power of two; probe on both sides of 2^126.
        let two_126 = Rational::integer(1i128 << 126);
        assert!(!two_126.is_big());
        let doubled = two_126 * Rational::integer(2);
        assert!(doubled.is_big(), "2^127 exceeds i128::MAX");
        let halved = doubled / Rational::integer(2);
        assert!(!halved.is_big(), "2^126 must demote back to the fast path");
        assert_eq!(halved, two_126);
        assert_eq!(halved.numerator(), 1i128 << 126);
    }

    #[test]
    fn handelman_numerator_1_6e57_is_exact() {
        // docs/plan/status/111-nra-handelman-cert.md: the exact derivation needs
        // a numerator around 1.6e57, which no i128 product can hold.
        let numerator = BigInt::from(16u32) * ten_pow(56);
        let target =
            Rational::from_big_rational(&BigRational::new(numerator.clone(), BigInt::from(7u32)))
                .expect("pool has room");
        assert!(target.is_big());
        // Reach the same value by exact arithmetic rather than by construction.
        let built = Rational::integer(16)
            * Rational::integer(10i128.pow(28))
            * Rational::integer(10i128.pow(28))
            / Rational::integer(7);
        assert_eq!(built, target);
        assert_eq!(built.numerator_big(), numerator);
        assert_eq!(built.denominator(), 7);
        assert_eq!(format!("{built}"), format!("{numerator}/7"));
    }

    #[test]
    fn growth_then_cancellation_retakes_the_fast_path() {
        let base = Rational::new(3, 7);
        let huge = Rational::integer(i128::MAX);
        let grown = base * huge * huge;
        assert!(grown.is_big(), "the intermediate must promote");
        let back = grown / huge / huge;
        assert!(
            !back.is_big(),
            "cancelling back into range must demote to the fast path"
        );
        assert_eq!(back, base);
        assert_eq!(back.numerator(), 3);
        assert_eq!(back.denominator(), 7);
    }

    #[test]
    fn eq_ord_and_hash_agree_across_representations() {
        // A value that fits must be identical whether it was built directly or
        // arrived by demotion from the big path.
        let direct = Rational::new(-5, 9);
        let huge = Rational::integer(i128::MAX);
        let round_tripped = direct * huge / huge;
        assert!(!round_tripped.is_big());
        assert_eq!(direct, round_tripped);
        assert_eq!(direct.cmp(&round_tripped), core::cmp::Ordering::Equal);
        assert_eq!(hash_of(direct), hash_of(round_tripped));

        // Two independently promoted equal big values must also agree.
        let big_a = Rational::integer(1i128 << 120) * Rational::integer(1i128 << 120);
        let big_b = Rational::integer(1i128 << 100)
            * Rational::integer(1i128 << 100)
            * Rational::integer(1i128 << 40);
        assert!(big_a.is_big() && big_b.is_big());
        assert_eq!(big_a, big_b);
        assert_eq!(hash_of(big_a), hash_of(big_b));
        assert!(big_a > direct);
        assert!(direct < big_a);
    }

    #[test]
    fn comparison_never_declines() {
        // Cross-multiplication of these two overflows i128, so before ADR-1702
        // `checked_cmp` returned None here.
        let a = Rational::new(i128::MAX, 3);
        let b = Rational::new(i128::MAX - 1, 5);
        assert_eq!(a.checked_cmp(&b), Some(core::cmp::Ordering::Greater));
        assert!(a > b);
        // Big vs small, both directions.
        let huge = Rational::integer(1i128 << 100) * Rational::integer(1i128 << 100);
        assert!(huge > a);
        assert!((-huge) < b);
    }

    #[test]
    fn checked_div_still_declines_on_zero() {
        assert_eq!(
            Rational::integer(1).checked_div(Rational::zero()),
            None,
            "division by zero is not an overflow and must still decline"
        );
        let huge = Rational::integer(1i128 << 100) * Rational::integer(1i128 << 100);
        assert_eq!(huge.checked_div(Rational::zero()), None);
    }

    #[test]
    fn recip_and_neg_across_the_boundary() {
        let huge = Rational::integer(1i128 << 100) * Rational::integer(1i128 << 100);
        let inverse = huge.recip();
        assert!(inverse.is_big());
        assert_eq!(inverse.numerator(), 1);
        assert_eq!(inverse * huge, Rational::integer(1));
        assert_eq!(-(-huge), huge);
        // i128::MIN negation used to be the one `checked_neg` failure.
        let min = Rational::integer(i128::MIN);
        let negated = min.checked_neg().expect("promotes instead of declining");
        assert!(negated.is_big());
        assert_eq!(negated + min, Rational::zero());
    }

    #[test]
    fn zero_and_integer_predicates_hold_for_promoted_values() {
        let huge = Rational::integer(1i128 << 100) * Rational::integer(1i128 << 100);
        assert!(!huge.is_zero());
        assert!(huge.is_integer());
        let fraction = huge / Rational::integer(3);
        assert!(fraction.is_big());
        assert!(!fraction.is_integer());
        assert!(!fraction.is_zero());
        assert_eq!(huge - huge, Rational::zero());
        assert!(!(huge - huge).is_big(), "zero always fits i128");
    }

    /// Seeded xorshift64* — a property test must be reproducible, and this
    /// avoids a new dev-dependency.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }

        /// A signed `i128` centred on zero, without a lossy cast.
        fn next_i128(&mut self) -> i128 {
            i128::from(self.next()) - i128::from(u64::MAX / 2)
        }

        /// A rational whose magnitude deliberately straddles `2^127`: the shift
        /// pushes the numerator up to the ceiling, and one operand in three is
        /// squared so that PROMOTED values are inputs too, not just outputs.
        fn rational(&mut self) -> Rational {
            let shift = u32::try_from(self.next() % 127).expect("shift < 127");
            let num = self.next_i128() << shift;
            let den = self.next_i128() | 1;
            let base = Rational::new(num, den);
            if self.next() % 3 == 0 {
                base * base
            } else {
                base
            }
        }
    }

    #[test]
    fn every_operation_agrees_with_bigrational() {
        let mut rng = Rng(0x5EED_1702);
        for _ in 0..2000 {
            let a = rng.rational();
            let b = rng.rational();
            let (ab, bb) = (a.to_big_rational(), b.to_big_rational());

            assert_eq!(
                (a + b).to_big_rational(),
                ab.clone() + bb.clone(),
                "add disagrees for {a:?} + {b:?}"
            );
            assert_eq!(
                (a - b).to_big_rational(),
                ab.clone() - bb.clone(),
                "sub disagrees for {a:?} - {b:?}"
            );
            assert_eq!(
                (a * b).to_big_rational(),
                ab.clone() * bb.clone(),
                "mul disagrees for {a:?} * {b:?}"
            );
            assert_eq!(
                (-a).to_big_rational(),
                -ab.clone(),
                "neg disagrees for {a:?}"
            );
            assert_eq!(a.cmp(&b), ab.cmp(&bb), "cmp disagrees for {a:?} vs {b:?}");
            if !b.is_zero() {
                assert_eq!(
                    (a / b).to_big_rational(),
                    ab.clone() / bb.clone(),
                    "div disagrees for {a:?} / {b:?}"
                );
            }
            if !a.is_zero() {
                assert_eq!(
                    a.recip().to_big_rational(),
                    ab.recip(),
                    "recip disagrees for {a:?}"
                );
            }
            // Representation is canonical: a value that fits i128 is small.
            let sum = a + b;
            if sum.checked_numerator().is_some() && sum.checked_denominator().is_some() {
                assert!(!sum.is_big(), "{sum:?} fits i128 but stayed promoted");
            }
        }
    }

    #[test]
    fn pool_capacity_is_reported() {
        assert_eq!(Rational::big_pool_capacity(), 1 << 20);
        let before = Rational::big_pool_len();
        let _ = Rational::integer(1i128 << 100) * Rational::integer(1i128 << 100);
        assert!(
            Rational::big_pool_len() >= before,
            "the pool is append-only"
        );
        assert!(Rational::big_pool_len() <= Rational::big_pool_capacity());
    }
}
