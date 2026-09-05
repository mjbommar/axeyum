//! Exact rational numbers for linear real arithmetic (ADR-0015, ADR-1702).
//!
//! A [`Rational`] is a normalized fraction: the denominator is always positive,
//! the fraction is in lowest terms, and zero is `0/1`. Normalization makes the
//! representation canonical, so structural `Eq`/`Hash` coincide with value
//! equality and the type can key the term interner.
//!
//! # Two representations, one value
//!
//! Per **ADR-1702** the type carries an `i128` **fast path** and an
//! arbitrary-precision **slow path**:
//!
//! - **small** — `num`/`den` are the `i128` fraction directly, `den > 0`.
//! - **big** — the value did not fit `i128`, so it lives in a process-global
//!   deduplicating pool and `num` holds its pool id, marked by `den == 0`
//!   (impossible for a small, whose denominator is always positive).
//!
//! The struct is still two `i128` fields, so it stays `Copy` and its size and
//! layout are unchanged; that matters because `Rational` is consumed by value in
//! thousands of places and is a field of the interned `TermNode::RealConst`.
//!
//! # Promotion is OPT-IN, per route
//!
//! Two families of operations, deliberately:
//!
//! | family | on `i128` overflow | who uses it |
//! |---|---|---|
//! | `new`, `checked_*`, the `Add`/`Sub`/`Mul`/`Div`/`Neg` operators | **declines** (`None`) or panics, exactly as before ADR-1702 | everything, by default |
//! | `wide_new`, `wide_add`, `wide_sub`, `wide_mul`, `wide_div`, `wide_neg`, `wide_recip` | **promotes** to arbitrary precision | a route that has opted in |
//!
//! Making promotion the *global* meaning of the existing operations was
//! implemented first and then measured, and it broke `axeyum-cas`: 25 unit tests
//! failed and about seven more stopped terminating, because that crate uses
//! `i128` exhaustion as a **cost bound and a termination argument** — a Gröbner
//! reduction, a Wilf–Zeilberger certificate search or a zero test that used to
//! decline instead runs away on values with hundreds of digits. `i128` range is
//! load-bearing there, so widening it is a per-route decision, not a property of
//! the type.
//!
//! Any result that fits `i128` again is **demoted** back, on both families, so
//! the fast path is retaken after transient growth and each value has exactly
//! one representation — which is what keeps derived `Eq` (and the `TermNode`
//! interner that depends on it) correct. The declining family accepts promoted
//! operands: it computes exactly and then demotes, returning `None` if the
//! result does not fit. So a promoted value never produces a wrong answer
//! anywhere, only a decline.
//!
//! Comparison is the exception that is not opt-in: `Ord`/`wide_cmp` are always
//! exact and can never fail, because comparing allocates no pool entry. Before
//! ADR-1702 `Ord::cmp` panicked on a cross-multiplication overflow.
//!
//! # Soundness
//!
//! Both paths compute the same mathematical value — `BigRational` normalizes to
//! the same canonical form and the demotion check (`BigInt::to_i128`) is exact —
//! so no verdict built on this type can change. Only an `unknown` caused by
//! running out of range, on a route that opted in, can become a decision. The
//! pool id is never observable: `Eq`, `Ord`, `Hash` and `Display` are all defined
//! on the value, so a run that assigns different ids still produces identical
//! output.
//!
//! # The one hazard
//!
//! [`Rational::numerator`] and [`Rational::denominator`] return `i128` and
//! therefore **panic** on a promoted value rather than truncate. Saturating would
//! turn an out-of-range value into a silently wrong one, which this project does
//! not accept. A route that opts into `wide_*` must therefore either keep
//! promoted values internal or use [`Rational::checked_numerator`] /
//! [`Rational::numerator_big`] (and the `denominator` counterparts).

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
#[inline]
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
#[inline]
fn small_add(lhs_num: i128, lhs_den: i128, rhs_num: i128, rhs_den: i128) -> Option<Rational> {
    // Both operands are in lowest terms with positive denominators.
    let common = gcd(lhs_den.unsigned_abs(), rhs_den.unsigned_abs());
    #[allow(clippy::cast_possible_wrap)]
    let common = common as i128;
    // `common` divides both denominators exactly and is >= 1.
    let lhs_scale = lhs_den / common;
    let rhs_scale = rhs_den / common;
    let scaled_lhs = lhs_num.checked_mul(rhs_scale)?;
    let scaled_rhs = rhs_num.checked_mul(lhs_scale)?;
    let num = scaled_lhs.checked_add(scaled_rhs)?;
    // The least common denominator: lhs_scale * rhs_den == lcm(lhs_den, rhs_den).
    let den = lhs_scale.checked_mul(rhs_den)?;
    small_new(num, den)
}

/// Multiplies two **small** fractions with cross-cancellation, or `None` on
/// `i128` overflow. See [`Rational::checked_mul`].
#[inline]
fn small_mul(lhs_num: i128, lhs_den: i128, rhs_num: i128, rhs_den: i128) -> Option<Rational> {
    let negative = (lhs_num < 0) != (rhs_num < 0);
    let mut a = lhs_num.unsigned_abs();
    let mut b = lhs_den.unsigned_abs();
    let mut c = rhs_num.unsigned_abs();
    let mut d = rhs_den.unsigned_abs();
    let cross_lhs = gcd(a, d);
    if cross_lhs > 1 {
        a /= cross_lhs;
        d /= cross_lhs;
    }
    let cross_rhs = gcd(c, b);
    if cross_rhs > 1 {
        c /= cross_rhs;
        b /= cross_rhs;
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
#[inline]
fn small_cmp(
    lhs_num: i128,
    lhs_den: i128,
    rhs_num: i128,
    rhs_den: i128,
) -> Option<core::cmp::Ordering> {
    // Cheap exact shortcuts that never multiply.
    if lhs_den == rhs_den {
        return Some(lhs_num.cmp(&rhs_num));
    }
    if (lhs_num < 0) != (rhs_num < 0) {
        return Some(lhs_num.cmp(&rhs_num));
    }
    // Compare over the least common denominator (both denominators are
    // positive, so the direction is preserved).
    let common = gcd(lhs_den.unsigned_abs(), rhs_den.unsigned_abs());
    #[allow(clippy::cast_possible_wrap)]
    let common = common as i128;
    let lhs = lhs_num.checked_mul(rhs_den / common)?;
    let rhs = rhs_num.checked_mul(lhs_den / common)?;
    Some(lhs.cmp(&rhs))
}

/// The **cold** half of every arithmetic operation: at least one operand is
/// promoted, or the `i128` path overflowed.
///
/// These are deliberately `#[cold]` + `#[inline(never)]`. Inlining a body that
/// touches `BigRational` into the hot wrapper cost **12%** on the
/// `simplex_incremental_check_feasible_lp` benchmark (229 us -> 256 us,
/// measured 2026-09-05 over five pinned runs each); outlining them puts the
/// wrapper back to a pair of compares plus the unchanged `i128` arithmetic.
mod cold {
    use super::{BigRational, Rational};

    #[cold]
    #[inline(never)]
    pub(super) fn add(lhs: Rational, rhs: Rational) -> BigRational {
        lhs.to_big_rational() + rhs.to_big_rational()
    }

    #[cold]
    #[inline(never)]
    pub(super) fn sub(lhs: Rational, rhs: Rational) -> BigRational {
        lhs.to_big_rational() - rhs.to_big_rational()
    }

    #[cold]
    #[inline(never)]
    pub(super) fn mul(lhs: Rational, rhs: Rational) -> BigRational {
        lhs.to_big_rational() * rhs.to_big_rational()
    }

    #[cold]
    #[inline(never)]
    pub(super) fn div(lhs: Rational, rhs: Rational) -> BigRational {
        lhs.to_big_rational() / rhs.to_big_rational()
    }

    #[cold]
    #[inline(never)]
    pub(super) fn neg(value: Rational) -> BigRational {
        -value.to_big_rational()
    }

    #[cold]
    #[inline(never)]
    pub(super) fn recip(value: Rational) -> BigRational {
        value.to_big_rational().recip()
    }

    #[cold]
    #[inline(never)]
    pub(super) fn cmp(lhs: Rational, rhs: Rational) -> core::cmp::Ordering {
        lhs.to_big_rational().cmp(&rhs.to_big_rational())
    }
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

    /// Demotes an arbitrary-precision value to the `i128` fast path, or `None`
    /// if it does not fit. **Never** interns, so this is the conversion the
    /// declining (`checked_*`) family uses.
    #[inline]
    fn demote_only(value: &BigRational) -> Option<Self> {
        let (num, den) = (value.numer().to_i128()?, value.denom().to_i128()?);
        debug_assert!(den > 0, "BigRational denominator must be positive");
        Some(Self { num, den })
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
    /// This is a **declining** constructor: it does not promote (see the module
    /// documentation for why promotion is opt-in). [`Rational::wide_new`] is the
    /// promoting counterpart.
    ///
    /// # Panics
    ///
    /// Panics if `den` is zero, or on `i128` overflow during normalization.
    pub fn new(num: i128, den: i128) -> Self {
        assert!(den != 0, "rational denominator must be non-zero");
        small_new(num, den).expect("rational normalization in range")
    }

    /// Creates `num/den` normalized to lowest terms, returning `None` instead of
    /// panicking on `i128` overflow during normalization (`den` zero is a usage
    /// error and still panics).
    ///
    /// This is the overflow-graceful counterpart of [`Rational::new`], used by
    /// the ground evaluator (the soundness trust anchor) so an out-of-range
    /// rational becomes a graceful error rather than a panic or a wrong wrapped
    /// value. It **declines** rather than promoting; [`Rational::wide_new`] is
    /// the promoting counterpart.
    ///
    /// # Panics
    ///
    /// Panics if `den` is zero (a denominator-zero rational is a usage error,
    /// not an overflow). `i128` overflow during normalization returns `None`.
    #[must_use]
    pub fn checked_new(num: i128, den: i128) -> Option<Self> {
        assert!(den != 0, "rational denominator must be non-zero");
        small_new(num, den)
    }

    /// Creates `num/den` normalized to lowest terms, **promoting** to arbitrary
    /// precision instead of declining on `i128` overflow (ADR-1702).
    ///
    /// Returns `None` only if the value needs the big-rational pool and the pool
    /// is at capacity ([`Rational::big_pool_capacity`]).
    ///
    /// # Panics
    ///
    /// Panics if `den` is zero (a usage error, not an overflow).
    #[must_use]
    pub fn wide_new(num: i128, den: i128) -> Option<Self> {
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
    /// Declining, like the rest of the `checked_*`/operator family: it does not
    /// promote. [`Rational::wide_recip`] is the promoting counterpart.
    ///
    /// # Panics
    ///
    /// Panics if this is zero, or on `i128` overflow during normalization.
    #[must_use]
    pub fn recip(self) -> Self {
        assert!(!self.is_zero(), "reciprocal of zero rational");
        self.wide_recip()
            .filter(|r| !r.is_big())
            .expect("rational reciprocal in range")
    }

    /// Exact negation, returning `None` on `i128` overflow (`num == i128::MIN`).
    ///
    /// **Declines rather than promotes** (ADR-1702): a result outside `i128` is
    /// `None`, exactly as before promotion existed. A *promoted operand* — which
    /// only the opt-in `wide_*` family can produce — is negated exactly and then
    /// demoted, so this still never returns a wrong value.
    #[must_use]
    #[inline]
    pub fn checked_neg(self) -> Option<Self> {
        if self.is_small() {
            return Some(Self {
                num: self.num.checked_neg()?,
                den: self.den,
            });
        }
        Self::demote_only(&cold::neg(self))
    }

    /// Exact addition, returning `None` on `i128` overflow.
    ///
    /// **Declines rather than promotes** (ADR-1702); [`Rational::wide_add`] is
    /// the promoting counterpart.
    ///
    /// Adds over the **least** common denominator rather than the product one:
    /// with `g = gcd(b, d)`, `a/b + c/d = (a·(d/g) + c·(b/g)) / ((b/g)·d)`. The
    /// naive `(a·d + c·b)/(b·d)` overflows on intermediates whose reduced result
    /// fits comfortably, which in the exact-rational simplex is not academic: a
    /// single overflow inside `pivot_and_update` abandons the whole
    /// branch-and-bound tree as `unknown` (it was the true cause of the `QF_LIA`
    /// `CAV_2009_benchmarks` residual, misreported as a node-budget exhaustion).
    #[inline]
    #[must_use]
    pub fn checked_add(self, other: Self) -> Option<Self> {
        if self.is_small() && other.is_small() {
            return small_add(self.num, self.den, other.num, other.den);
        }
        Self::demote_only(&cold::add(self, other))
    }

    /// Exact subtraction, returning `None` on `i128` overflow.
    ///
    /// **Declines rather than promotes** (ADR-1702); [`Rational::wide_sub`] is
    /// the promoting counterpart.
    #[inline]
    #[must_use]
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        if self.is_small() && other.is_small() {
            return small_add(self.num, self.den, other.num.checked_neg()?, other.den);
        }
        Self::demote_only(&cold::sub(self, other))
    }

    /// Exact multiplication, returning `None` on `i128` overflow.
    ///
    /// **Declines rather than promotes** (ADR-1702); [`Rational::wide_mul`] is
    /// the promoting counterpart.
    ///
    /// **Cross-cancels before multiplying** — `gcd(a, d)` and `gcd(c, b)` are
    /// divided out of `(a/b)·(c/d)` first — so only the *reduced* product has to
    /// fit in `i128`. Multiplying first and reducing after loses every product
    /// whose unreduced form overflows even though the answer is small.
    #[inline]
    #[must_use]
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        if self.is_small() && other.is_small() {
            return small_mul(self.num, self.den, other.num, other.den);
        }
        Self::demote_only(&cold::mul(self, other))
    }

    /// Exact division, returning `None` on division by zero or `i128` overflow.
    ///
    /// **Declines rather than promotes** (ADR-1702); [`Rational::wide_div`] is
    /// the promoting counterpart.
    #[inline]
    #[must_use]
    pub fn checked_div(self, other: Self) -> Option<Self> {
        if other.is_zero() {
            return None;
        }
        if self.is_small() && other.is_small() {
            // The reciprocal is normalized first: `small_mul` assumes both
            // operands are in lowest terms with a POSITIVE denominator, and
            // `(other.den, other.num)` is not when `other` is negative.
            let recip = small_new(other.den, other.num)?;
            return small_mul(self.num, self.den, recip.num, recip.den);
        }
        Self::demote_only(&cold::div(self, other))
    }

    /// Total ordering that returns `None` on `i128` overflow during the
    /// cross-multiplication comparison, instead of panicking.
    ///
    /// Kept declining for two small operands so the pre-ADR-1702 behaviour is
    /// preserved exactly. A *promoted* operand is compared at full precision,
    /// which allocates nothing and cannot fail. [`Rational::wide_cmp`] is the
    /// always-exact counterpart.
    #[inline]
    #[must_use]
    pub fn checked_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        if self.is_small() && other.is_small() {
            return small_cmp(self.num, self.den, other.num, other.den);
        }
        Some(self.wide_cmp(other))
    }

    // --- ADR-1702: the opt-in PROMOTING family -------------------------------
    //
    // These are the only operations that can create a value outside `i128`.
    // Promotion is opt-in per route, not a change in the meaning of the existing
    // operations, because it was MEASURED to break routes that use `i128`
    // exhaustion as their cost bound — see the module documentation.

    /// Exact reciprocal, **promoting** past `i128` instead of declining.
    ///
    /// Returns `None` if this is zero, or if the big-rational pool is at
    /// capacity ([`Rational::big_pool_capacity`]).
    #[must_use]
    pub fn wide_recip(self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        if self.is_small()
            && let Some(small) = small_new(self.den, self.num)
        {
            return Some(small);
        }
        Self::from_big(&cold::recip(self))
    }

    /// Exact negation, **promoting** past `i128` instead of declining.
    ///
    /// Returns `None` only if the big-rational pool is at capacity.
    #[must_use]
    #[inline]
    pub fn wide_neg(self) -> Option<Self> {
        if self.is_small()
            && let Some(num) = self.num.checked_neg()
        {
            return Some(Self { num, den: self.den });
        }
        Self::from_big(&cold::neg(self))
    }

    /// Exact addition, **promoting** past `i128` instead of declining.
    ///
    /// Returns `None` only if the big-rational pool is at capacity.
    #[inline]
    #[must_use]
    pub fn wide_add(self, other: Self) -> Option<Self> {
        if self.is_small()
            && other.is_small()
            && let Some(small) = small_add(self.num, self.den, other.num, other.den)
        {
            return Some(small);
        }
        Self::from_big(&cold::add(self, other))
    }

    /// Exact subtraction, **promoting** past `i128` instead of declining.
    ///
    /// Returns `None` only if the big-rational pool is at capacity.
    #[inline]
    #[must_use]
    pub fn wide_sub(self, other: Self) -> Option<Self> {
        if self.is_small()
            && other.is_small()
            && let Some(neg) = other.num.checked_neg()
            && let Some(small) = small_add(self.num, self.den, neg, other.den)
        {
            return Some(small);
        }
        Self::from_big(&cold::sub(self, other))
    }

    /// Exact multiplication, **promoting** past `i128` instead of declining.
    ///
    /// Returns `None` only if the big-rational pool is at capacity.
    #[inline]
    #[must_use]
    pub fn wide_mul(self, other: Self) -> Option<Self> {
        if self.is_small()
            && other.is_small()
            && let Some(small) = small_mul(self.num, self.den, other.num, other.den)
        {
            return Some(small);
        }
        Self::from_big(&cold::mul(self, other))
    }

    /// Exact division, **promoting** past `i128` instead of declining.
    ///
    /// Returns `None` on division by zero, or if the big-rational pool is at
    /// capacity.
    #[inline]
    #[must_use]
    pub fn wide_div(self, other: Self) -> Option<Self> {
        if other.is_zero() {
            return None;
        }
        if self.is_small()
            && other.is_small()
            && let Some(recip) = small_new(other.den, other.num)
            && let Some(small) = small_mul(self.num, self.den, recip.num, recip.den)
        {
            return Some(small);
        }
        Self::from_big(&cold::div(self, other))
    }

    /// Total ordering that is always exact and can never decline: a comparison
    /// outside `i128` range falls back to arbitrary precision, which allocates no
    /// pool entry.
    #[inline]
    #[must_use]
    pub fn wide_cmp(&self, other: &Self) -> core::cmp::Ordering {
        if self.is_small()
            && other.is_small()
            && let Some(ordering) = small_cmp(self.num, self.den, other.num, other.den)
        {
            return ordering;
        }
        cold::cmp(*self, *other)
    }
}

impl core::ops::Div for Rational {
    type Output = Self;

    /// Exact division.
    ///
    /// # Panics
    ///
    /// Panics on division by zero or `i128` overflow.
    #[allow(clippy::suspicious_arithmetic_impl)] // division is multiply-by-reciprocal
    fn div(self, other: Self) -> Self {
        self.checked_div(other).expect("rational division overflow")
    }
}

impl core::ops::Neg for Rational {
    type Output = Self;

    /// Exact negation.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow (only `num == i128::MIN`).
    fn neg(self) -> Self {
        self.checked_neg().expect("rational negation in range")
    }
}

impl core::ops::Add for Rational {
    type Output = Self;

    /// Exact addition.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow.
    fn add(self, other: Self) -> Self {
        self.checked_add(other).expect("rational add overflow")
    }
}

impl core::ops::Sub for Rational {
    type Output = Self;

    /// Exact subtraction.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow.
    fn sub(self, other: Self) -> Self {
        self.checked_sub(other).expect("rational sub overflow")
    }
}

impl core::ops::Mul for Rational {
    type Output = Self;

    /// Exact multiplication.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow.
    fn mul(self, other: Self) -> Self {
        self.checked_mul(other).expect("rational mul overflow")
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    /// Always exact, and since ADR-1702 it can no longer panic: a comparison
    /// whose cross-multiplication leaves `i128` falls back to arbitrary
    /// precision, which allocates nothing. Comparison is the one operation where
    /// widening cannot cost anything, so it is not opt-in.
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.wide_cmp(other)
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
#[inline]
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

    // --- ADR-1702 --------------------------------------------------------------
    //
    // Promotion is OPT-IN: the `checked_*`/operator family must still decline on
    // `i128` overflow (routes such as `axeyum-cas` use that as a cost bound), and
    // only the `wide_*` family promotes. The first test below is the one that
    // distinguishes the two designs.

    #[test]
    fn the_checked_family_declines_exactly_where_the_wide_family_promotes() {
        let two_100 = Rational::integer(1i128 << 100);
        // Declining family: unchanged by ADR-1702.
        assert_eq!(two_100.checked_mul(two_100), None);
        assert_eq!(two_100.checked_add(Rational::integer(i128::MAX)), None);
        assert_eq!(Rational::integer(i128::MIN).checked_neg(), None);
        assert_eq!(Rational::checked_new(i128::MIN, -1), None);
        // Promoting family: the same operations succeed and are exact.
        let product = two_100.wide_mul(two_100).expect("promotes");
        assert!(product.is_big());
        assert_eq!(product.numerator_big(), BigInt::from(1u32) << 200u32);
        assert!(
            Rational::integer(i128::MIN)
                .wide_neg()
                .expect("promotes")
                .is_big(),
            "-i128::MIN needs the wide path"
        );
        assert!(
            Rational::wide_new(i128::MIN, -1)
                .expect("promotes")
                .is_big()
        );
    }

    #[test]
    #[should_panic(expected = "rational mul overflow")]
    fn the_multiplication_operator_still_panics_on_overflow() {
        let two_100 = Rational::integer(1i128 << 100);
        let _ = two_100 * two_100;
    }

    #[test]
    fn product_across_2_127_promotes_and_is_exact() {
        // 2^100 * 2^100 = 2^200, well past i128::MAX (< 2^127).
        let two_100 = Rational::integer(1i128 << 100);
        let product = two_100.wide_mul(two_100).expect("promotes");
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
        let _ = two_100.wide_mul(two_100).expect("promotes").numerator();
    }

    #[test]
    fn just_below_and_just_above_the_i128_ceiling() {
        // i128::MAX is not a power of two; probe on both sides of 2^126.
        let two_126 = Rational::integer(1i128 << 126);
        assert!(!two_126.is_big());
        let doubled = two_126.wide_mul(Rational::integer(2)).expect("promotes");
        assert!(doubled.is_big(), "2^127 exceeds i128::MAX");
        let halved = doubled.wide_div(Rational::integer(2)).expect("demotes");
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
            .wide_mul(Rational::integer(10i128.pow(28)))
            .and_then(|r| r.wide_mul(Rational::integer(10i128.pow(28))))
            .and_then(|r| r.wide_div(Rational::integer(7)))
            .expect("promotes");
        assert_eq!(built, target);
        assert_eq!(built.numerator_big(), numerator);
        assert_eq!(built.denominator(), 7);
        assert_eq!(format!("{built}"), format!("{numerator}/7"));
    }

    #[test]
    fn growth_then_cancellation_retakes_the_fast_path() {
        let base = Rational::new(3, 7);
        let huge = Rational::integer(i128::MAX);
        let grown = base
            .wide_mul(huge)
            .and_then(|r| r.wide_mul(huge))
            .expect("promotes");
        assert!(grown.is_big(), "the intermediate must promote");
        let back = grown
            .wide_div(huge)
            .and_then(|r| r.wide_div(huge))
            .expect("demotes");
        assert!(
            !back.is_big(),
            "cancelling back into range must demote to the fast path"
        );
        assert_eq!(back, base);
        assert_eq!(back.numerator(), 3);
        assert_eq!(back.denominator(), 7);
    }

    #[test]
    fn the_declining_family_accepts_a_promoted_operand_exactly_or_declines() {
        let huge = Rational::integer(1i128 << 100)
            .wide_mul(Rational::integer(1i128 << 100))
            .expect("promotes");
        // Result still out of range: decline, never a wrong value, never a panic.
        assert_eq!(huge.checked_mul(Rational::integer(2)), None);
        assert_eq!(huge.checked_add(Rational::integer(1)), None);
        // Result back in range: exact.
        assert_eq!(huge.checked_sub(huge), Some(Rational::zero()));
        assert_eq!(
            huge.checked_div(huge),
            Some(Rational::integer(1)),
            "a promoted operand whose quotient fits must come back exact"
        );
    }

    #[test]
    fn eq_ord_and_hash_agree_across_representations() {
        // A value that fits must be identical whether it was built directly or
        // arrived by demotion from the big path.
        let direct = Rational::new(-5, 9);
        let huge = Rational::integer(i128::MAX);
        let round_tripped = direct
            .wide_mul(huge)
            .and_then(|r| r.wide_div(huge))
            .expect("round trip");
        assert!(!round_tripped.is_big());
        assert_eq!(direct, round_tripped);
        assert_eq!(direct.cmp(&round_tripped), core::cmp::Ordering::Equal);
        assert_eq!(hash_of(direct), hash_of(round_tripped));

        // Two independently promoted equal big values must also agree.
        let big_a = Rational::integer(1i128 << 120)
            .wide_mul(Rational::integer(1i128 << 120))
            .expect("promotes");
        let big_b = Rational::integer(1i128 << 100)
            .wide_mul(Rational::integer(1i128 << 100))
            .and_then(|r| r.wide_mul(Rational::integer(1i128 << 40)))
            .expect("promotes");
        assert!(big_a.is_big() && big_b.is_big());
        assert_eq!(big_a, big_b);
        assert_eq!(hash_of(big_a), hash_of(big_b));
        assert!(big_a > direct);
        assert!(direct < big_a);
    }

    #[test]
    fn comparison_never_declines_and_never_panics() {
        // Cross-multiplication of these two overflows i128, so `Ord::cmp` used to
        // panic here. Comparison allocates nothing, so it is exact unconditionally.
        let a = Rational::new(i128::MAX, 3);
        let b = Rational::new(i128::MAX - 1, 5);
        assert_eq!(a.wide_cmp(&b), core::cmp::Ordering::Greater);
        assert!(a > b);
        // Big vs small, both directions.
        let huge = Rational::integer(1i128 << 100)
            .wide_mul(Rational::integer(1i128 << 100))
            .expect("promotes");
        assert!(huge > a);
        assert!(huge.wide_neg().expect("promotes") < b);
    }

    #[test]
    fn division_by_zero_still_declines_on_both_families() {
        assert_eq!(Rational::integer(1).checked_div(Rational::zero()), None);
        assert_eq!(Rational::integer(1).wide_div(Rational::zero()), None);
        let huge = Rational::integer(1i128 << 100)
            .wide_mul(Rational::integer(1i128 << 100))
            .expect("promotes");
        assert_eq!(huge.checked_div(Rational::zero()), None);
        assert_eq!(huge.wide_div(Rational::zero()), None);
        assert_eq!(Rational::zero().wide_recip(), None);
    }

    #[test]
    fn recip_and_neg_across_the_boundary() {
        let huge = Rational::integer(1i128 << 100)
            .wide_mul(Rational::integer(1i128 << 100))
            .expect("promotes");
        let inverse = huge.wide_recip().expect("promotes");
        assert!(inverse.is_big());
        assert_eq!(inverse.numerator(), 1);
        assert_eq!(inverse.wide_mul(huge), Some(Rational::integer(1)));
        assert_eq!(huge.wide_neg().and_then(Rational::wide_neg), Some(huge));
        // i128::MIN negation is the one `checked_neg` failure, and it still is.
        let min = Rational::integer(i128::MIN);
        assert_eq!(min.checked_neg(), None);
        let negated = min.wide_neg().expect("promotes instead of declining");
        assert!(negated.is_big());
        assert_eq!(negated.wide_add(min), Some(Rational::zero()));
    }

    #[test]
    fn zero_and_integer_predicates_hold_for_promoted_values() {
        let huge = Rational::integer(1i128 << 100)
            .wide_mul(Rational::integer(1i128 << 100))
            .expect("promotes");
        assert!(!huge.is_zero());
        assert!(huge.is_integer());
        let fraction = huge.wide_div(Rational::integer(3)).expect("promotes");
        assert!(fraction.is_big());
        assert!(!fraction.is_integer());
        assert!(!fraction.is_zero());
        assert_eq!(huge.wide_sub(huge), Some(Rational::zero()));
        assert!(
            !huge.wide_sub(huge).expect("exact").is_big(),
            "zero always fits i128"
        );
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
        /// squared through the wide path so that PROMOTED values are inputs too,
        /// not just outputs.
        fn rational(&mut self) -> Rational {
            let shift = u32::try_from(self.next() % 127).expect("shift < 127");
            let num = self.next_i128() << shift;
            let den = self.next_i128() | 1;
            // `wide_new`, not `new`: the generator deliberately produces
            // `i128::MIN` numerators, which the declining constructor panics on.
            let base = Rational::wide_new(num, den).expect("pool has room");
            if self.next().is_multiple_of(3) {
                base.wide_mul(base).expect("pool has room")
            } else {
                base
            }
        }
    }

    #[test]
    fn every_wide_operation_agrees_with_bigrational() {
        let mut rng = Rng(0x5EED_1702);
        for _ in 0..2000 {
            let a = rng.rational();
            let b = rng.rational();
            let (ab, bb) = (a.to_big_rational(), b.to_big_rational());

            assert_eq!(
                a.wide_add(b).expect("pool").to_big_rational(),
                ab.clone() + bb.clone(),
                "add disagrees for {a:?} + {b:?}"
            );
            assert_eq!(
                a.wide_sub(b).expect("pool").to_big_rational(),
                ab.clone() - bb.clone(),
                "sub disagrees for {a:?} - {b:?}"
            );
            assert_eq!(
                a.wide_mul(b).expect("pool").to_big_rational(),
                ab.clone() * bb.clone(),
                "mul disagrees for {a:?} * {b:?}"
            );
            assert_eq!(
                a.wide_neg().expect("pool").to_big_rational(),
                -ab.clone(),
                "neg disagrees for {a:?}"
            );
            assert_eq!(
                a.wide_cmp(&b),
                ab.cmp(&bb),
                "cmp disagrees for {a:?} vs {b:?}"
            );
            if !b.is_zero() {
                assert_eq!(
                    a.wide_div(b).expect("pool").to_big_rational(),
                    ab.clone() / bb.clone(),
                    "div disagrees for {a:?} / {b:?}"
                );
            }
            if !a.is_zero() {
                assert_eq!(
                    a.wide_recip().expect("pool").to_big_rational(),
                    ab.recip(),
                    "recip disagrees for {a:?}"
                );
            }

            // Representation is canonical: a value that fits i128 is small.
            let sum = a.wide_add(b).expect("pool");
            if sum.checked_numerator().is_some() && sum.checked_denominator().is_some() {
                assert!(!sum.is_big(), "{sum:?} fits i128 but stayed promoted");
            }

            // The declining family never disagrees with the wide one: it either
            // returns the same value or declines.
            for (checked, wide) in [
                (a.checked_add(b), a.wide_add(b)),
                (a.checked_sub(b), a.wide_sub(b)),
                (a.checked_mul(b), a.wide_mul(b)),
            ] {
                if let Some(value) = checked {
                    assert!(!value.is_big(), "the declining family must stay in i128");
                    assert_eq!(Some(value), wide, "declining and wide disagree");
                }
            }
        }
    }

    #[test]
    fn pool_capacity_is_reported() {
        assert_eq!(Rational::big_pool_capacity(), 1 << 20);
        let before = Rational::big_pool_len();
        let _ = Rational::integer(1i128 << 100).wide_mul(Rational::integer(1i128 << 100));
        assert!(
            Rational::big_pool_len() >= before,
            "the pool is append-only"
        );
        assert!(Rational::big_pool_len() <= Rational::big_pool_capacity());
    }
}
