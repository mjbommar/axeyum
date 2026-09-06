//! Exact mathematical integers outside the `i128` reference range
//! (ADR-0376's recorded design, realized as ADR-1702 slice 2).
//!
//! # Why a second variant and not a wider payload
//!
//! `TermNode::IntConst(i128)` and `Value::Int(i128)` bound the modeled `Int`
//! range to `i128`, and the SMT-LIB front door turned a wider numeral into
//! `SmtError::Unsupported`, so 26 of the 200 QF_UFLIA competition files — EVM
//! `uint256` bounds from Certora — never reached the solver at all.
//!
//! ADR-0376 measured the two ways out and recorded the answer. Changing the
//! payload to `BigInt` in place was rejected: it breaks the `*value` deref at
//! every `IntConst` match site, turns every `arena.int_const(0)` on the hot LIA
//! path into a heap allocation, and pushes bignum into the core the way ADR-0045
//! forbids. What it recorded instead is the shape this module implements — a
//! **second variant for the out-of-native-range case**, exactly as
//! [`crate::wide::WideUint`] / `TermNode::WideBvConst` already do for
//! bit-vectors wider than 128 bits. The ~390 `Value::Int` and ~210 `IntConst`
//! sites keep their `i128` payload and stay correct **by construction**: they
//! cannot observe a wide value at all, so there is no truncation to get wrong.
//!
//! The payload is [`num_bigint::BigInt`] rather than a hand-rolled limb type.
//! `WideUint` exists because bit-vectors need fixed-width *wrapping* semantics
//! mod `2^width` plus a `width` field, which `BigInt` deliberately does not
//! model; mathematical integers are unbounded and exact, which `BigInt` is. The
//! *structural* precedent is what is copied here, not the payload type.
//!
//! # The canonicality invariant
//!
//! `TermNode` and `Value` derive `Hash`/`Eq`, and `TermNode` keys the arena's
//! intern table, so a value with two representations silently breaks structural
//! sharing. The invariant is therefore:
//!
//! > **A well-formed `WideIntConst(w)` / `Value::WideInt(w)` satisfies
//! > `w.checked_i128().is_none()`.** Every `i128`-representable integer is
//! > `IntConst` / `Value::Int`, never the wide variant.
//!
//! It is enforced at the two constructors that build those nodes —
//! [`crate::TermArena::int_const_big`] and [`crate::Value::from_wide_int`] —
//! which **demote** back to the narrow variant whenever the value fits, the same
//! way `TermArena::bv_const` promotes to `WideBvConst` above 128 bits. `BigInt`
//! is itself canonical (num-bigint normalizes sign and magnitude, so there is no
//! `-0` and no leading-zero limb), so with the demotion rule each integer has
//! exactly one node.
//!
//! # The one hazard, and the discipline ADR-1702 set for it
//!
//! [`WideInt::to_i128`] returns `i128` and **panics** on a value that does not
//! fit, rather than truncating or saturating — the same contract
//! [`crate::wide::WideUint::to_u128`] and `Rational::numerator` already carry.
//! Turning an out-of-range value into a silently wrong one is the failure mode
//! this project does not accept, and a wrong `sat`/`unsat` built on a truncated
//! bound is exactly what truncation would produce. Callers that may hold a wide
//! value use [`WideInt::checked_i128`] or [`WideInt::big`].

use std::cmp::Ordering;
use std::fmt;

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

/// An exact mathematical integer with an arbitrary-precision payload.
///
/// The type itself can hold any integer; the *node* invariant — that a
/// `TermNode::WideIntConst` / [`Value::WideInt`](crate::Value::WideInt) never
/// holds an `i128`-representable value — is enforced by the arena and `Value`
/// constructors, not by this type. That split mirrors
/// [`WideUint`](crate::wide::WideUint), which likewise represents narrow widths
/// perfectly well while `TermArena::bv_const` decides which variant a given
/// constant becomes.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WideInt(BigInt);

impl WideInt {
    /// Wraps an arbitrary-precision integer.
    #[must_use]
    pub fn from_big(value: BigInt) -> Self {
        Self(value)
    }

    /// Widens an `i128`.
    #[must_use]
    pub fn from_i128(value: i128) -> Self {
        Self(BigInt::from(value))
    }

    /// Parses a decimal numeral, with an optional leading `-`.
    ///
    /// Returns `None` for anything that is not a well-formed decimal integer.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        text.parse::<BigInt>().ok().map(Self)
    }

    /// The arbitrary-precision payload.
    #[must_use]
    pub fn big(&self) -> &BigInt {
        &self.0
    }

    /// Consumes this value and returns its payload.
    #[must_use]
    pub fn into_big(self) -> BigInt {
        self.0
    }

    /// Whether the value is representable as an `i128`.
    ///
    /// A well-formed wide *node* always answers `false`; see the module docs.
    #[must_use]
    pub fn fits_i128(&self) -> bool {
        self.0.to_i128().is_some()
    }

    /// The value as an `i128`, or `None` when it does not fit.
    ///
    /// This is the non-panicking accessor a route holding a possibly-wide value
    /// should use.
    #[must_use]
    pub fn checked_i128(&self) -> Option<i128> {
        self.0.to_i128()
    }

    /// The value as an `i128`.
    ///
    /// # Panics
    ///
    /// Panics if the value does not fit an `i128`. It deliberately does **not**
    /// truncate or saturate: an out-of-range bound silently narrowed to a
    /// different number is how a wrong `sat`/`unsat` gets produced, and a panic
    /// on an internal invariant violation is strictly better than a wrong
    /// verdict. Nothing reachable from parsed user input may call this without
    /// first checking [`WideInt::fits_i128`] — see the admission check in
    /// `axeyum-solver`.
    #[must_use]
    pub fn to_i128(&self) -> i128 {
        match self.0.to_i128() {
            Some(value) => value,
            None => panic!(
                "to_i128 on a {}-bit integer literal (`{}`); use checked_i128 or big",
                self.bits(),
                self.0
            ),
        }
    }

    /// The number of bits in the magnitude (`0` for zero).
    #[must_use]
    pub fn bits(&self) -> u64 {
        self.0.bits()
    }

    /// Whether the value is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    /// Whether the value is strictly negative.
    #[must_use]
    pub fn is_negative(&self) -> bool {
        self.0.is_negative()
    }

    /// Exact negation.
    #[must_use]
    pub fn neg(&self) -> Self {
        Self(-&self.0)
    }

    /// Exact addition.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self(&self.0 + &other.0)
    }

    /// Exact subtraction.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        Self(&self.0 - &other.0)
    }

    /// Exact multiplication.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        Self(&self.0 * &other.0)
    }

    /// Exact absolute value.
    #[must_use]
    pub fn abs(&self) -> Self {
        Self(self.0.abs())
    }

    /// Ordering against another exact integer.
    #[must_use]
    pub fn compare(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl fmt::Display for WideInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl From<i128> for WideInt {
    fn from(value: i128) -> Self {
        Self::from_i128(value)
    }
}

impl From<BigInt> for WideInt {
    fn from(value: BigInt) -> Self {
        Self::from_big(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn two_pow(n: u32) -> WideInt {
        WideInt::from_big(BigInt::from(2u8).pow(n))
    }

    #[test]
    fn i128_max_fits_and_the_next_value_does_not() {
        assert!(WideInt::from_i128(i128::MAX).fits_i128());
        assert!(WideInt::from_i128(i128::MIN).fits_i128());
        let past = WideInt::from_i128(i128::MAX).add(&WideInt::from_i128(1));
        assert!(!past.fits_i128());
        assert_eq!(past.checked_i128(), None);
        assert_eq!(past.to_string(), "170141183460469231731687303715884105728");
    }

    #[test]
    fn to_i128_returns_the_value_when_it_fits() {
        assert_eq!(WideInt::from_i128(-7).to_i128(), -7);
        assert_eq!(WideInt::from_i128(i128::MAX).to_i128(), i128::MAX);
        assert_eq!(WideInt::from_i128(i128::MIN).to_i128(), i128::MIN);
    }

    /// The ADR-1702 hazard contract, stated as a test: an out-of-range value
    /// must **panic**, never come back as a different (truncated or saturated)
    /// number. A patch replacing the panic with `to_i128().unwrap_or(...)`,
    /// with a wrapping cast, or with a saturating one, fails here.
    #[test]
    #[should_panic(expected = "to_i128 on a 256-bit integer literal")]
    fn to_i128_panics_rather_than_truncating_a_wide_value() {
        let _ = two_pow(255).to_i128();
    }

    #[test]
    fn a_wide_value_never_narrows_to_a_plausible_wrong_number() {
        // `2^128` truncated to the low 128 bits is 0, and saturated is
        // `i128::MAX`. Both are values a caller could mistake for real, which is
        // why neither is offered.
        let value = two_pow(128);
        assert_eq!(value.checked_i128(), None);
        assert!(!value.fits_i128());
        assert_eq!(value.bits(), 129);
    }

    #[test]
    fn arithmetic_is_exact_across_the_i128_boundary() {
        let a = two_pow(200);
        let b = two_pow(200);
        assert_eq!(a.add(&b), two_pow(201));
        assert_eq!(a.sub(&b), WideInt::from_i128(0));
        assert_eq!(a.mul(&WideInt::from_i128(2)), two_pow(201));
        assert_eq!(a.neg().abs(), a);
        assert!(a.neg().is_negative());
        assert!(a.sub(&b).is_zero());
        assert_eq!(a.compare(&b), Ordering::Equal);
        assert_eq!(two_pow(201).compare(&a), Ordering::Greater);
    }

    /// A product that grows out of `i128` and cancels back into range: the type
    /// stays exact throughout, so the demotion the arena performs on the way out
    /// sees the right number.
    #[test]
    fn a_chain_that_leaves_and_re_enters_the_i128_range_is_exact() {
        let grown = WideInt::from_i128(i128::MAX).mul(&WideInt::from_i128(1_000));
        assert!(!grown.fits_i128());
        let back = grown.sub(&WideInt::from_i128(i128::MAX).mul(&WideInt::from_i128(999)));
        assert_eq!(back.checked_i128(), Some(i128::MAX));
    }

    #[test]
    fn parse_round_trips_the_evm_word_and_rejects_non_numerals() {
        let word = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
        let parsed = WideInt::parse(word).expect("2^256 - 1 parses");
        assert_eq!(parsed.to_string(), word);
        assert_eq!(parsed.bits(), 256);
        assert_eq!(WideInt::parse("-42").map(|v| v.to_i128()), Some(-42));
        assert!(WideInt::parse("12x").is_none());
        assert!(WideInt::parse("").is_none());
    }

    #[test]
    fn equality_and_hash_are_value_based() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let a = two_pow(300);
        let b = WideInt::parse(&two_pow(300).to_string()).expect("round trip");
        assert_eq!(a, b);
        let mut ha = DefaultHasher::new();
        let mut hb = DefaultHasher::new();
        a.hash(&mut ha);
        b.hash(&mut hb);
        assert_eq!(ha.finish(), hb.finish());
    }
}
