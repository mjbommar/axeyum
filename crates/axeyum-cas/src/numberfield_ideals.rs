//! Ideals, prime splitting, class numbers, and primitive elements.
//!
//! Item 4 of the CAS *Next Ten*, second wave, and the sibling of
//! [`crate::numberfield`], which owns **element** arithmetic. This module owns
//! the **ideal** side: the ring of integers of a quadratic field, ideals as
//! `ℤ`-modules in Hermite normal form, how a rational prime decomposes, how a
//! principal ideal factors, the class number of an imaginary quadratic
//! discriminant, and a primitive element for a compositum.
//!
//! Everything here is exact and arbitrary-precision: coefficients are
//! [`BigInt`] and [`BigRational`], nothing overflows the way the `i128` core
//! does, and no `f64` appears. Every collection that reaches an output is a
//! [`BTreeMap`] or [`BTreeSet`], so results are deterministic.
//!
//! # What this module computes
//!
//! - [`QuadraticOrder`] — `O_K = ℤ + ℤω` for squarefree `d`, carrying the one
//!   relation `ω² = t·ω + n`. The `d ≡ 1 (mod 4)` case (`ω = (1+√d)/2`) and the
//!   `d ≡ 2, 3` case (`ω = √d`) differ only in `(t, n)`, so nothing downstream
//!   branches on which one it is.
//! - [`Ideal`] — a nonzero ideal as `ℤ·a + ℤ·(b + cω)` with `a > 0`, `c > 0`,
//!   `0 ≤ b < a`. That normal form is **canonical**, so `==` *is* ideal
//!   equality; [`Ideal::norm`] is `a·c`, [`Ideal::contains_element`] and
//!   [`Ideal::contains`] are read straight off the basis.
//! - [`QuadraticOrder::multiply_ideals`] — `I·J`, with
//!   [`IdealProductCertificate`].
//! - [`QuadraticOrder::split_prime`] — Dedekind's criterion over the minimal
//!   polynomial `x² − t·x − n` of `ω` modulo `p`, with
//!   [`PrimeSplittingCertificate`] and a [`SplittingType`].
//! - [`QuadraticOrder::factor_ideal`] and
//!   [`QuadraticOrder::factor_principal_ideal`] — `I = ∏ 𝔭ᵢ^{eᵢ}`, with
//!   [`IdealFactorizationCertificate`].
//! - [`class_number`] — `h(D)` for `D < 0` by enumerating reduced
//!   [`BinaryQuadraticForm`]s, with [`ClassNumberCertificate`].
//! - [`primitive_element`] — `θ = α + k·β` for `ℚ(α, β)`, with
//!   [`PrimitiveElementCertificate`] carrying `α` and `β` back as polynomials
//!   in `θ`.
//!
//! # What this module reuses (and does not reinvent)
//!
//! - **[`QuadraticField`]** decides that `d` is squarefree and admissible;
//!   [`QuadraticOrder::from_field`] takes an already-built one rather than
//!   repeating the check. Building this module found that
//!   [`QuadraticField::new`] refused `d = −1`, so `ℚ(i)` was unreachable even
//!   though [`crate::numberfield::GaussianInt`] sits beside it; that is fixed
//!   in `numberfield.rs` and `ℤ[i]` is now a worked example here.
//! - **[`crate::ntheory::factorize`]** (trial division then Pollard rho)
//!   factors `N(I)` — it is the only integer factorizer in the workspace, and
//!   it is `i128`, so an ideal whose norm exceeds that range is **declined**
//!   with [`IdealDecline::MagnitudeOutOfRange`], never guessed at.
//! - **[`crate::ntheory::is_prime`]** (Miller–Rabin) decides primality both in
//!   the producer and, independently, inside every `verify`.
//! - **[`crate::ntheory_advanced::sqrt_mod`]** (Tonelli–Shanks) supplies the
//!   root of `x² ≡ D (mod p)` that names the two primes above a split `p`.
//! - **[`crate::ntheory_advanced::kronecker_symbol`]** is what every splitting
//!   certificate re-derives its splitting type from — deliberately a different
//!   route from the producer's root-counting, so the two have to agree.
//! - **[`NumberField`] and [`crate::numberfield::Element`]** carry the
//!   compositum: `NumberField::new` decides irreducibility through the crate's
//!   Berlekamp–Zassenhaus factorizer, and `Element::inverse` is what makes the
//!   `ℚ(θ)[y]` Euclidean algorithm possible.
//! - **The `BigRational` `ℚ[x]` helpers and the exact determinant** in
//!   `numberfield.rs`, which became `pub(crate)` for this module. The Sylvester
//!   resultant here is new; the determinant under it is not.
//!
//! What is **not** reused: [`crate::resultant`] is univariate and `i128`. The
//! resultant needed here, `Res_y(f(θ − k·y), g(y))`, is bivariate — its
//! coefficients are polynomials in `θ` — so it is computed by evaluation at
//! `deg f · deg g + 1` rational points and Lagrange interpolation, each
//! evaluation being one exact Sylvester determinant. That is sound because the
//! leading coefficient of `f(θ − k·y)` in `y` is the **constant** `(−k)^{deg f}`,
//! so no evaluation can drop the degree.
//!
//! # What is certified, and what is `uncertified`
//!
//! Every certificate's `verify` re-derives the claim from the recorded data
//! and never consults how the producer found it.
//!
//! | producer | certificate | guards |
//! |---|---|---|
//! | [`QuadraticOrder::multiply_ideals`] | [`IdealProductCertificate`] | order parameters match the radicand; all three ideals pass [`Ideal::admissible_in`]; the four basis products are re-derived and compared elementwise **and** by count; `N(IJ) = N(I)·N(J)`; the Hermite form re-run over the products equals the recorded one |
//! | [`QuadraticOrder::split_prime`] | [`PrimeSplittingCertificate`] | `p` is prime; the recorded `D` is the one `d` determines; the splitting type equals the recomputed Kronecker symbol `(D/p)`; the factor count matches the type; split means two different primes and ramified means one twice; the factors multiply back to `(p)` through verified product certificates; each factor has norm `p` (split, ramified) or `p²` (inert) |
//! | [`QuadraticOrder::factor_ideal`] | [`IdealFactorizationCertificate`] | the target is an ideal; no exponent is zero; each factor is a prime ideal, meaning its norm is `p` or `p²` for a rational prime and it appears among the primes `split_prime` puts over that `p`; `∏ N(𝔭ᵢ)^{eᵢ} = N(I)`; `∏ 𝔭ᵢ^{eᵢ} = I` |
//! | [`class_number`] | [`ClassNumberCertificate`] | `D < 0` and `D ≡ 0, 1 (mod 4)`; every listed form has discriminant `D`, is positive definite, primitive and reduced, all recomputed; no form repeats; and the whole region is **recounted by a different traversal** |
//! | [`primitive_element`] | [`PrimitiveElementCertificate`] | `f` and `g` are monic and non-constant; `k ≠ 0`; the recorded minimal polynomial of `θ` is monic of degree `deg f · deg g`, squarefree, and irreducible over ℚ; and, inside `ℚ[x]/(R)`, the recorded `α` satisfies `f`, the recorded `β` satisfies `g`, and `α + k·β = θ` |
//!
//! **The theorem behind the class number, and its hypothesis.** *Every
//! positive definite primitive integral binary quadratic form of discriminant
//! `D < 0` is `SL₂(ℤ)`-equivalent to exactly one reduced form* — reduced
//! meaning `|b| ≤ a ≤ c` with `b ≥ 0` whenever `|b| = a` or `a = c`. Its
//! hypothesis is `D < 0` and `D ≡ 0` or `1 (mod 4)`; both are checked, and the
//! producer declines rather than assumes them. **Uniqueness** is what turns
//! "the listed forms are pairwise different" into "the listed classes are
//! pairwise inequivalent", which is why no composition law and no explicit
//! equivalence test are needed — and none are shipped.
//!
//! **`uncertified`, and why.**
//!
//! - [`QuadraticOrder::multiply`] and [`QuadraticOrder::element_norm`] on
//!   [`OrderElement`], and [`QuadraticOrder::ideal_power`]. Checking a product
//!   costs a product; a certificate for them would be the producer in a hat.
//!   The same reasoning as [`crate::fps`] and [`crate::numberfield`]. The
//!   certified route for a power is the product certificate on each step,
//!   which is what [`IdealFactorizationCertificate::verify`] actually runs.
//! - [`Ideal::contains_element`], [`Ideal::contains`], [`Ideal::norm`] and
//!   [`Ideal::basis`] are one-line reads of the canonical basis.
//! - **The exponents [`QuadraticOrder::factor_ideal`] finds by containment
//!   testing are not certified as exponents.** Only the product identity is,
//!   and that is deliberate: a wrong exponent cannot survive `verify`, so the
//!   search is allowed to be a heuristic. A search that falls short is reported
//!   as [`IdealDecline::FactorizationIncomplete`], never shipped.
//! - **Non-principality is not certified.** The test that `𝔭₂ ⊂ ℤ[√−5]` is not
//!   principal is a bounded exhaustive sweep over the norm form in the test
//!   module, not a certificate object. A `Principality` certificate would need
//!   either a class-group *law* or a general norm-equation solver; neither is
//!   in this slice.
//! - **The Kronecker symbol, `factorize`, `is_prime` and `sqrt_mod` are
//!   trusted as reused routines.** They are `i128` and this module is bignum,
//!   so every crossing point converts explicitly and declines on overflow with
//!   [`IdealDecline::MagnitudeOutOfRange`] or refuses with
//!   [`IdealCertificateError::MagnitudeOutOfRange`]; but their *answers* are
//!   not re-derived here.
//!
//! **One guard was measured redundant and removed rather than kept for
//! appearances.** The splitting certificate used to run
//! [`Ideal::admissible_in`] on every factor before multiplying them; deleting
//! that loop killed zero tests, because `product_of_ideals` verifies a product
//! certificate per step and *that* certificate already checks admissibility.
//! It is gone. Three other guards were found inert by the same sweep — the
//! generator-product **count** check, and the `right`/`product` admissibility
//! calls in the product certificate — and those got the missing forgeries
//! instead, because unlike the first they are reachable.
//!
//! # Out of scope, deliberately
//!
//! - **Composition of forms (the class group law).** This module gives the
//!   class group as a *set* with its cardinality. Gauss composition, the group
//!   structure, and the correspondence with ideal classes are not here.
//! - **Real quadratic class groups.** `h(D)` for `D > 0` needs the regulator
//!   and the continued-fraction cycle of reduced indefinite forms, which is a
//!   different algorithm from the one shipped; [`class_number`] declines with
//!   [`IdealDecline::DiscriminantNotNegative`] rather than answering wrongly.
//!   The related real-quadratic *unit* computation does exist, in
//!   [`crate::numberfield::QuadraticField::fundamental_unit`].
//! - **Rings of integers of general number fields.** The `ℤ + ℤω` presentation
//!   is quadratic-only; a Round 2 / Round 4 maximal-order computation for
//!   higher degree is not here, so [`primitive_element`] gives the *field*
//!   `ℚ(α, β)` and says nothing about its ring of integers.
//! - **Galois groups, ramification groups, different and conductor.**
//! - **Ideal classes as a group, class field theory, `L`-functions.**
//! - **Non-maximal orders as objects.** [`class_number`] happily takes a
//!   non-fundamental `D` — it counts forms of that discriminant, which is the
//!   form class number of the order of discriminant `D` — but
//!   [`QuadraticOrder`] itself is always the maximal order.
//!
//! # Cost profile
//!
//! **ADVISORY.** Measured 2026-09-05 on a shared host at load average 12.02,
//! `--release`, single-threaded, with the enumeration and its independent
//! recount timed separately:
//!
//! | `|D|` | `h(D)` | produce | verify (recount) |
//! |---|---|---|---|
//! | `10³` | 10 | 47 µs | 35 µs |
//! | `10⁴` | 20 | 92 µs | 244 µs |
//!
//! The shape, independent of the clock: the reduced region has
//! `|b| ≤ a ≤ c` and `4ac = b² − D`, so both `a` and `b` are `O(√|D|)` and the
//! whole enumeration is `Θ(|D|)` bignum operations. That is why
//! [`CLASS_NUMBER_DISCRIMINANT_BOUND`] exists and why the producer declines
//! above it instead of hanging a gate. Verification costs the same order as
//! production, and at `10⁴` slightly more, because the recount walks the region
//! by `a` and then by every `b` in `−a ..= a` rather than by divisors.
//!
//! Everything else in this module is small at the sizes it admits: ideal
//! multiplication is four `BigInt` products plus a 2×2 Hermite form; a prime
//! splitting is one Tonelli–Shanks; an ideal factorization is one `i128`
//! integer factorization (which dominates it, and is the reason for the
//! magnitude declines) plus one containment test per candidate exponent. The
//! whole 70-test module runs in **0.16 s to 0.33 s of wall clock,
//! single-threaded, in a debug build** across two runs on this shared host,
//! the slowest single test being the degree-6 compositum at 0.039 s to
//! 0.065 s — so no per-operation split was worth measuring below that.

use core::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use std::collections::{BTreeMap, BTreeSet};

use crate::ntheory::{factorize, is_prime};
use crate::ntheory_advanced::{kronecker_symbol, sqrt_mod};
use crate::numberfield::{
    CertificateError, Element, NumberField, QuadraticField, matrix_determinant, poly_add,
    poly_degree, poly_ext_gcd, poly_mul, poly_scale, poly_trim, rat_one, rat_zero,
};

/// Largest `|D|` for which [`class_number`] runs its enumeration.
///
/// The reduced-form region has area proportional to `|D|`, so the enumeration
/// is linear in `|D|` and a large discriminant would hang the gate rather than
/// answer. Above this the producer declines with
/// [`IdealDecline::DiscriminantTooLarge`].
pub const CLASS_NUMBER_DISCRIMINANT_BOUND: i64 = 10_000_000;

/// Largest `k` tried by [`primitive_element`] before it declines.
///
/// Only finitely many `k` fail — at most one per coincidence
/// `α_i + k·β_j = α_{i'} + k·β_{j'}` — so a decline here means the search was
/// cut short, never that no primitive element exists.
pub const PRIMITIVE_ELEMENT_SEARCH_BOUND: i64 = 64;

// ---------------------------------------------------------------------------
// Refusals and declines
// ---------------------------------------------------------------------------

/// Why an ideal-theoretic certificate was refused.
///
/// Each variant names a distinct, independently reachable guard.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdealCertificateError {
    /// The Hermite basis has `a ≤ 0`.
    BasisLeadingNotPositive,
    /// The Hermite basis has `c ≤ 0`.
    BasisDenominatorNotPositive,
    /// The Hermite basis is not reduced: `b` is outside `0 ≤ b < a`.
    BasisOffDiagonalNotReduced,
    /// `c ∤ a`, so `ℤa + ℤ(b + cω)` is not closed under multiplication by `ω`.
    BasisDenominatorDoesNotDivideLeading,
    /// `c ∤ b`, so the module is not closed under multiplication by `ω`.
    BasisDenominatorDoesNotDivideOffDiagonal,
    /// `a·c ∤ N(b + cω)`, the remaining closure condition.
    BasisNotClosedUnderOmega,
    /// The recorded generator products are not the products of the recorded
    /// bases. Carries the index of the first disagreeing product.
    GeneratorProductMismatch {
        /// Index into the certificate's generator-product list.
        index: usize,
    },
    /// The Hermite form re-derived from the generator products is not the
    /// recorded product ideal.
    ProductHermiteMismatch,
    /// `N(IJ) ≠ N(I)·N(J)`.
    ProductNormMismatch,
    /// The certificate's order parameters are not the ones its squarefree
    /// radicand determines.
    OrderParametersMismatch,
    /// The rational number a splitting certificate is about is not prime.
    SplittingBaseNotPrime,
    /// The recorded splitting type is not the one the Kronecker symbol
    /// `(D/p)` re-derives.
    SplittingTypeMismatch {
        /// The symbol `(D/p)` recomputed by the checker.
        symbol: i32,
    },
    /// The number of recorded prime ideals does not match the splitting type:
    /// two for split and ramified, one for inert.
    SplittingFactorCountMismatch {
        /// The count the certificate carries.
        found: usize,
        /// The count the recorded splitting type requires.
        expected: usize,
    },
    /// A split certificate records two equal prime ideals, or a ramified one
    /// records two different ones.
    SplittingFactorDistinctnessMismatch,
    /// A recorded prime ideal does not have the norm its splitting type
    /// requires — `p` when split or ramified, `p²` when inert.
    PrimeIdealNormMismatch {
        /// Index into the factor list.
        index: usize,
    },
    /// The product of the recorded prime ideals is not the principal ideal
    /// `(p)`.
    SplittingProductMismatch,
    /// A factorization records an exponent of zero, which asserts nothing.
    ZeroExponent {
        /// Index into the factor list.
        index: usize,
    },
    /// A factor of an ideal factorization is not one of the prime ideals over
    /// its own norm's rational prime.
    FactorIsNotAPrimeIdeal {
        /// Index into the factor list.
        index: usize,
    },
    /// The norm of a factor is neither a rational prime nor the square of one.
    FactorNormNotAPrimePower {
        /// Index into the factor list.
        index: usize,
    },
    /// The product of the recorded prime powers is not the target ideal.
    FactorizationProductMismatch,
    /// The product of the recorded factor norms is not the target's norm.
    FactorizationNormMismatch,
    /// A magnitude in the certificate is past the `i128` range of the reused
    /// primality and factorization routines, so the claim cannot be
    /// re-derived. Never treated as checked.
    MagnitudeOutOfRange,
    /// A class-number certificate carries a non-negative discriminant; only
    /// the imaginary quadratic case is in scope.
    DiscriminantNotNegative,
    /// A discriminant that is not `≡ 0` or `1 (mod 4)`, so no binary quadratic
    /// form has it.
    DiscriminantNotAdmissible,
    /// A listed form does not have the certificate's discriminant.
    FormDiscriminantMismatch {
        /// Index into the form list.
        index: usize,
    },
    /// A listed form has `a ≤ 0`, so it is not positive definite.
    FormNotPositiveDefinite {
        /// Index into the form list.
        index: usize,
    },
    /// A listed form has `gcd(a, b, c) > 1`, so it is imprimitive and does not
    /// count towards the class number.
    FormNotPrimitive {
        /// Index into the form list.
        index: usize,
    },
    /// A listed form violates `|b| ≤ a ≤ c`, or the boundary sign convention
    /// `b ≥ 0` when `|b| = a` or `a = c`.
    FormNotReduced {
        /// Index into the form list.
        index: usize,
    },
    /// Two listed forms are equal, so the list overcounts.
    FormsNotDistinct {
        /// Index of the repeated form.
        index: usize,
    },
    /// The independent recount over the reduced region found a different
    /// number of forms.
    ClassNumberRecountMismatch {
        /// The count the certificate claims.
        claimed: usize,
        /// The count the checker's own enumeration found.
        recounted: usize,
    },
    /// A primitive-element certificate whose `f` or `g` is constant, zero, or
    /// not monic.
    GeneratorPolynomialNotMonic,
    /// A primitive-element certificate with `k = 0`, for which `α + kβ = α`
    /// generates only `ℚ(α)`.
    PrimitiveElementMultiplierZero,
    /// The recorded minimal polynomial of `θ` is not monic of degree
    /// `deg f · deg g`.
    CompositumDegreeMismatch {
        /// The degree recorded.
        found: usize,
        /// The degree `deg f · deg g` required.
        expected: usize,
    },
    /// The recorded minimal polynomial of `θ` has a repeated root, so `θ` does
    /// not have degree `deg f · deg g`.
    CompositumNotSquarefree,
    /// The recorded minimal polynomial of `θ` is reducible over ℚ, or the
    /// reused factorizer declined; either way `ℚ[θ]` was not established to be
    /// a field.
    CompositumNotIrreducible,
    /// The recorded expression for `α` in `θ` does not satisfy `f`.
    AlphaDoesNotSatisfyF,
    /// The recorded expression for `β` in `θ` does not satisfy `g`.
    BetaDoesNotSatisfyG,
    /// The recorded expressions do not satisfy `α + k·β = θ`.
    PrimitiveElementRelationFails,
}

impl fmt::Display for IdealCertificateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// Why a producer in this module declined to answer.
///
/// A decline is an honest "did not run", never a claim about the input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdealDecline {
    /// The zero ideal, or the zero element, for which the operation is not
    /// defined.
    ZeroInput,
    /// A magnitude past the `i128` range of the reused integer factorizer and
    /// primality test.
    MagnitudeOutOfRange,
    /// The rational number the caller offered as a prime is not prime.
    NotPrime,
    /// Tonelli–Shanks declined for this prime, so the root of the `ω` minimal
    /// polynomial that names the split could not be computed.
    SqrtModDeclined {
        /// The prime for which no square root was produced.
        prime: i128,
    },
    /// `|D|` exceeds [`CLASS_NUMBER_DISCRIMINANT_BOUND`].
    DiscriminantTooLarge {
        /// The bound that was exceeded.
        bound: i64,
    },
    /// The discriminant is non-negative; only imaginary quadratic class
    /// numbers are in scope here.
    DiscriminantNotNegative,
    /// The discriminant is not `≡ 0` or `1 (mod 4)`.
    DiscriminantNotAdmissible,
    /// No `k` below [`PRIMITIVE_ELEMENT_SEARCH_BOUND`] made the resultant
    /// squarefree. The search was cut short; nothing is claimed about the
    /// compositum.
    NoPrimitiveElementFound {
        /// The bound that was reached.
        bound: i64,
    },
    /// One of the two minimal polynomials is not monic of degree at least one.
    GeneratorPolynomialNotMonic,
    /// The exponent search did not account for the whole norm, so the
    /// factorization would have been incomplete. Reachable only if a reused
    /// routine is wrong; declining beats shipping a partial product.
    FactorizationIncomplete,
}

impl fmt::Display for IdealDecline {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

// ---------------------------------------------------------------------------
// Integer helpers, written here so the module takes no new dependency
// ---------------------------------------------------------------------------

fn big_zero() -> BigInt {
    BigInt::zero()
}

fn big_one() -> BigInt {
    BigInt::one()
}

/// The non-negative greatest common divisor.
fn big_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut a = left.abs();
    let mut b = right.abs();
    while !b.is_zero() {
        let r = &a % &b;
        a = core::mem::replace(&mut b, r);
    }
    a
}

/// Extended Euclid: `(g, s, t)` with `s·left + t·right = g` and `g ≥ 0`.
fn big_ext_gcd(left: &BigInt, right: &BigInt) -> (BigInt, BigInt, BigInt) {
    let (mut old_r, mut r) = (left.clone(), right.clone());
    let (mut old_s, mut s) = (big_one(), big_zero());
    let (mut old_t, mut t) = (big_zero(), big_one());
    while !r.is_zero() {
        let quotient = &old_r / &r;
        let next_r = &old_r - &quotient * &r;
        old_r = core::mem::replace(&mut r, next_r);
        let next_s = &old_s - &quotient * &s;
        old_s = core::mem::replace(&mut s, next_s);
        let next_t = &old_t - &quotient * &t;
        old_t = core::mem::replace(&mut t, next_t);
    }
    if old_r.is_negative() {
        (-old_r, -old_s, -old_t)
    } else {
        (old_r, old_s, old_t)
    }
}

/// The representative of `value` in `0 ≤ r < modulus`, for `modulus > 0`.
fn big_mod_positive(value: &BigInt, modulus: &BigInt) -> BigInt {
    let mut r = value % modulus;
    if r.is_negative() {
        r += modulus;
    }
    r
}

/// The integer square root of a non-negative `value`, by Newton's method.
fn big_isqrt(value: &BigInt) -> BigInt {
    if value.is_negative() || value.is_zero() {
        return big_zero();
    }
    if value <= &BigInt::from(3) {
        return big_one();
    }
    let mut x = value.clone();
    let mut y = (&x + 1u32) / 2u32;
    while y < x {
        x.clone_from(&y);
        y = (&x + value / &x) / 2u32;
    }
    x
}

fn to_i128(value: &BigInt) -> Option<i128> {
    i128::try_from(value).ok()
}

// ---------------------------------------------------------------------------
// The quadratic order ℤ[ω] and its elements
// ---------------------------------------------------------------------------

/// The maximal order `O_K = ℤ + ℤω` of `K = ℚ(√d)` for squarefree `d`.
///
/// The single relation `ω² = t·ω + n` covers both cases:
///
/// | `d mod 4` | `ω` | `t` | `n` | discriminant `D = t² + 4n` |
/// |---|---|---|---|---|
/// | `1` | `(1 + √d)/2` | `1` | `(d − 1)/4` | `d` |
/// | `2, 3` | `√d` | `0` | `d` | `4d` |
///
/// Everything downstream — ideals, splitting, class numbers — is written
/// against `(t, n)` alone, so neither case is a special case in the code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuadraticOrder {
    radicand: BigInt,
    trace: BigInt,
    constant: BigInt,
    discriminant: BigInt,
}

impl QuadraticOrder {
    /// The maximal order of `ℚ(√d)`.
    ///
    /// # Errors
    ///
    /// Whatever [`QuadraticField::new`] refuses `d` with — `d ∈ {0, ±1}`, `d`
    /// not squarefree, or `|d|` past the reused squarefree test's range.
    pub fn new(radicand: &BigInt) -> Result<QuadraticOrder, CertificateError> {
        let field = QuadraticField::new(radicand)?;
        Ok(QuadraticOrder::from_field(&field))
    }

    /// The maximal order of an already-built [`QuadraticField`], reusing its
    /// squarefree check rather than repeating it.
    #[must_use]
    pub fn from_field(field: &QuadraticField) -> QuadraticOrder {
        let radicand = field.radicand().clone();
        let residue = big_mod_positive(&radicand, &BigInt::from(4));
        let (trace, constant) = if residue.is_one() {
            (big_one(), (&radicand - 1u32) / 4u32)
        } else {
            (big_zero(), radicand.clone())
        };
        let discriminant = &trace * &trace + 4u32 * &constant;
        QuadraticOrder {
            radicand,
            trace,
            constant,
            discriminant,
        }
    }

    /// The squarefree `d`.
    #[must_use]
    pub fn radicand(&self) -> &BigInt {
        &self.radicand
    }

    /// The field discriminant `D = t² + 4n`.
    #[must_use]
    pub fn discriminant(&self) -> &BigInt {
        &self.discriminant
    }

    /// `t` in `ω² = t·ω + n`.
    #[must_use]
    pub fn omega_trace(&self) -> &BigInt {
        &self.trace
    }

    /// `n` in `ω² = t·ω + n`.
    #[must_use]
    pub fn omega_constant(&self) -> &BigInt {
        &self.constant
    }

    /// The product of two elements. `uncertified`: checking a product costs a
    /// product, so a certificate would be the producer in a hat.
    #[must_use]
    pub fn multiply(&self, left: &OrderElement, right: &OrderElement) -> OrderElement {
        let (u1, v1) = (&left.rational, &left.omega);
        let (u2, v2) = (&right.rational, &right.omega);
        let rational = u1 * u2 + v1 * v2 * &self.constant;
        let omega = u1 * v2 + u2 * v1 + v1 * v2 * &self.trace;
        OrderElement { rational, omega }
    }

    /// The field norm `N(u + vω) = u² + t·u·v − n·v²`. `uncertified`; it is one
    /// multiplication, and the certified route is
    /// `crate::numberfield::Element::norm_trace`.
    #[must_use]
    pub fn element_norm(&self, element: &OrderElement) -> BigInt {
        let (u, v) = (&element.rational, &element.omega);
        u * u + &self.trace * u * v - &self.constant * v * v
    }

    /// `ω · (u + vω) = n·v + (u + t·v)·ω`.
    fn multiply_by_omega(&self, element: &OrderElement) -> OrderElement {
        OrderElement {
            rational: &self.constant * &element.omega,
            omega: &element.rational + &self.trace * &element.omega,
        }
    }

    /// The ideal generated by the given elements, in Hermite normal form.
    ///
    /// # Errors
    ///
    /// [`IdealDecline::ZeroInput`] when the generators span a module of rank
    /// less than two — the zero ideal, which has no Hermite basis here.
    pub fn ideal_from_generators(
        &self,
        generators: &[OrderElement],
    ) -> Result<Ideal, IdealDecline> {
        let mut rows: Vec<OrderElement> = Vec::with_capacity(generators.len() * 2);
        for generator in generators {
            rows.push(generator.clone());
            rows.push(self.multiply_by_omega(generator));
        }
        hermite_normal_form(&rows).ok_or(IdealDecline::ZeroInput)
    }

    /// The principal ideal `(α)`.
    ///
    /// # Errors
    ///
    /// [`IdealDecline::ZeroInput`] for `α = 0`.
    pub fn principal_ideal(&self, element: &OrderElement) -> Result<Ideal, IdealDecline> {
        self.ideal_from_generators(core::slice::from_ref(element))
    }

    /// The ideal generated by a rational integer, `(m)`.
    ///
    /// # Errors
    ///
    /// [`IdealDecline::ZeroInput`] for `m = 0`.
    pub fn rational_ideal(&self, value: &BigInt) -> Result<Ideal, IdealDecline> {
        self.principal_ideal(&OrderElement::new(value.clone(), big_zero()))
    }

    /// The unit ideal `(1) = O_K`.
    #[must_use]
    pub fn unit_ideal(&self) -> Ideal {
        Ideal {
            a: big_one(),
            b: big_zero(),
            c: big_one(),
        }
    }
}

/// An element `u + vω` of a [`QuadraticOrder`].
///
/// Ordered, so every collection in this module can be kept in a deterministic
/// order without a hash.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OrderElement {
    rational: BigInt,
    omega: BigInt,
}

impl OrderElement {
    /// The element `rational + omega·ω`.
    #[must_use]
    pub fn new(rational: BigInt, omega: BigInt) -> OrderElement {
        OrderElement { rational, omega }
    }

    /// The element `rational + omega·ω`, from machine integers.
    #[must_use]
    pub fn from_i64(rational: i64, omega: i64) -> OrderElement {
        OrderElement::new(BigInt::from(rational), BigInt::from(omega))
    }

    /// The coefficient of `1`.
    #[must_use]
    pub fn rational_part(&self) -> &BigInt {
        &self.rational
    }

    /// The coefficient of `ω`.
    #[must_use]
    pub fn omega_part(&self) -> &BigInt {
        &self.omega
    }

    /// Whether this is the zero element.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.rational.is_zero() && self.omega.is_zero()
    }
}

impl fmt::Display for OrderElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} + {}w", self.rational, self.omega)
    }
}

// ---------------------------------------------------------------------------
// Ideals in Hermite normal form
// ---------------------------------------------------------------------------

/// A nonzero ideal `I = ℤ·a + ℤ·(b + cω)` in Hermite normal form.
///
/// The normal form is `a > 0`, `c > 0`, `0 ≤ b < a`, which makes the
/// representation **canonical**: two ideals are equal exactly when their
/// triples are equal, so `==` is ideal equality and no separate equality
/// routine is needed. `N(I) = [O_K : I] = a·c`.
///
/// Construction by [`Ideal::from_hermite`] does **not** check that the triple
/// is closed under multiplication by `ω`; [`Ideal::admissible_in`] does, and
/// every certificate in this module runs it on every ideal it touches. That
/// split is deliberate: it is what lets a test forge an ideal and watch the
/// checker refuse it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ideal {
    a: BigInt,
    b: BigInt,
    c: BigInt,
}

impl Ideal {
    /// The ideal `ℤ·a + ℤ·(b + cω)`, **unchecked**.
    ///
    /// See the type documentation: admissibility is a certificate-time check,
    /// not a construction-time one.
    #[must_use]
    pub fn from_hermite(a: BigInt, b: BigInt, c: BigInt) -> Ideal {
        Ideal { a, b, c }
    }

    /// The ideal `ℤ·a + ℤ·(b + cω)`, **unchecked**, from machine integers.
    #[must_use]
    pub fn from_i64(a: i64, b: i64, c: i64) -> Ideal {
        Ideal::from_hermite(BigInt::from(a), BigInt::from(b), BigInt::from(c))
    }

    /// The smallest positive rational integer in the ideal.
    #[must_use]
    pub fn leading(&self) -> &BigInt {
        &self.a
    }

    /// The rational part of the second basis element.
    #[must_use]
    pub fn off_diagonal(&self) -> &BigInt {
        &self.b
    }

    /// The `ω` part of the second basis element.
    #[must_use]
    pub fn denominator(&self) -> &BigInt {
        &self.c
    }

    /// The two basis elements `a` and `b + cω`.
    #[must_use]
    pub fn basis(&self) -> [OrderElement; 2] {
        [
            OrderElement::new(self.a.clone(), big_zero()),
            OrderElement::new(self.b.clone(), self.c.clone()),
        ]
    }

    /// The absolute norm `N(I) = [O_K : I] = a·c`.
    #[must_use]
    pub fn norm(&self) -> BigInt {
        &self.a * &self.c
    }

    /// Whether `element ∈ I`, decided from the Hermite basis alone.
    ///
    /// `u + vω ∈ ℤa + ℤ(b + cω)` exactly when `c | v` and `a | u − (v/c)·b`.
    #[must_use]
    pub fn contains_element(&self, element: &OrderElement) -> bool {
        if self.c.is_zero() || self.a.is_zero() {
            return false;
        }
        if !(&element.omega % &self.c).is_zero() {
            return false;
        }
        let multiple = &element.omega / &self.c;
        ((&element.rational - &multiple * &self.b) % &self.a).is_zero()
    }

    /// Whether `other ⊆ self`, by testing `other`'s two basis elements.
    #[must_use]
    pub fn contains(&self, other: &Ideal) -> bool {
        other
            .basis()
            .iter()
            .all(|element| self.contains_element(element))
    }

    /// Re-derive that this triple really is an ideal of `order`.
    ///
    /// The six conditions are exactly closure of `ℤa + ℤ(b + cω)` under
    /// multiplication by `ω`, plus the normal-form conventions that make the
    /// representation canonical.
    ///
    /// # Errors
    ///
    /// One [`IdealCertificateError`] variant per condition, so a refusal says
    /// which one failed.
    pub fn admissible_in(&self, order: &QuadraticOrder) -> Result<(), IdealCertificateError> {
        // H1: a > 0.
        if !self.a.is_positive() {
            return Err(IdealCertificateError::BasisLeadingNotPositive);
        }
        // H2: c > 0.
        if !self.c.is_positive() {
            return Err(IdealCertificateError::BasisDenominatorNotPositive);
        }
        // H3: 0 ≤ b < a, the convention that makes the form canonical.
        if self.b.is_negative() || self.b >= self.a {
            return Err(IdealCertificateError::BasisOffDiagonalNotReduced);
        }
        // H4: c | a, forced by ω·a ∈ I.
        if !(&self.a % &self.c).is_zero() {
            return Err(IdealCertificateError::BasisDenominatorDoesNotDivideLeading);
        }
        // H5: c | b, forced by the same containment.
        if !(&self.b % &self.c).is_zero() {
            return Err(IdealCertificateError::BasisDenominatorDoesNotDivideOffDiagonal);
        }
        // H6: a·c | N(b + cω), forced by ω·(b + cω) ∈ I.
        let generator = OrderElement::new(self.b.clone(), self.c.clone());
        let norm = order.element_norm(&generator);
        if !(norm % self.norm()).is_zero() {
            return Err(IdealCertificateError::BasisNotClosedUnderOmega);
        }
        Ok(())
    }
}

impl fmt::Display for Ideal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {} + {}w]", self.a, self.b, self.c)
    }
}

/// The 2×2 Hermite normal form of the ℤ-module spanned by `rows`, in the basis
/// `(1, ω)`.
///
/// Returns `None` when the span has rank less than two.
fn hermite_normal_form(rows: &[OrderElement]) -> Option<Ideal> {
    let mut pivot: Option<(BigInt, BigInt)> = None;
    let mut leading = big_zero();
    for row in rows {
        let (mut x, mut y) = (row.rational.clone(), row.omega.clone());
        if y.is_zero() {
            leading = big_gcd(&leading, &x);
            continue;
        }
        if y.is_negative() {
            x = -x;
            y = -y;
        }
        match pivot.take() {
            None => pivot = Some((x, y)),
            Some((pivot_b, pivot_c)) => {
                let (gcd, s, t) = big_ext_gcd(&pivot_c, &y);
                let combined = &s * &pivot_b + &t * &x;
                let eliminated = (&pivot_c / &gcd) * &x - (&y / &gcd) * &pivot_b;
                leading = big_gcd(&leading, &eliminated);
                pivot = Some((combined, gcd));
            }
        }
    }
    let (pivot_b, c) = pivot?;
    if leading.is_zero() {
        return None;
    }
    let a = leading.abs();
    let b = big_mod_positive(&pivot_b, &a);
    Some(Ideal { a, b, c })
}

// ---------------------------------------------------------------------------
// Ideal multiplication, certified
// ---------------------------------------------------------------------------

/// `I·J` together with the products of the four pairs of basis elements that
/// generate it.
///
/// `verify` re-derives those four products from the recorded bases, re-runs
/// the Hermite normal form over them and their `ω`-multiples, and compares the
/// result to the recorded product — so it never consults how the producer got
/// there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdealProductCertificate {
    /// The squarefree radicand `d` of the field.
    pub radicand: BigInt,
    /// `t` in `ω² = t·ω + n`, recorded so a wrong order is refused rather than
    /// silently substituted.
    pub omega_trace: BigInt,
    /// `n` in `ω² = t·ω + n`.
    pub omega_constant: BigInt,
    /// The left factor.
    pub left: Ideal,
    /// The right factor.
    pub right: Ideal,
    /// The four products of basis elements, in the order
    /// `a₁a₂, a₁(b₂+c₂ω), (b₁+c₁ω)a₂, (b₁+c₁ω)(b₂+c₂ω)`.
    pub generator_products: Vec<OrderElement>,
    /// The claimed product ideal.
    pub product: Ideal,
}

impl IdealProductCertificate {
    /// The order the certificate's recorded parameters describe, refusing when
    /// they are not the ones `radicand` determines.
    fn order(&self) -> Result<QuadraticOrder, IdealCertificateError> {
        let order = QuadraticOrder::new(&self.radicand)
            .map_err(|_| IdealCertificateError::OrderParametersMismatch)?;
        if order.omega_trace() != &self.omega_trace
            || order.omega_constant() != &self.omega_constant
        {
            return Err(IdealCertificateError::OrderParametersMismatch);
        }
        Ok(order)
    }

    /// Re-derive `I·J` from the recorded bases alone.
    ///
    /// # Errors
    ///
    /// [`IdealCertificateError::OrderParametersMismatch`] for a wrong order;
    /// the [`Ideal::admissible_in`] refusals for any of the three ideals;
    /// [`IdealCertificateError::GeneratorProductMismatch`] naming the first
    /// wrong product; [`IdealCertificateError::ProductHermiteMismatch`] when
    /// the recomputed Hermite form differs; and
    /// [`IdealCertificateError::ProductNormMismatch`] when
    /// `N(IJ) ≠ N(I)·N(J)`.
    pub fn verify(&self) -> Result<(), IdealCertificateError> {
        let order = self.order()?;
        // P1..P3: all three ideals really are ideals of this order.
        self.left.admissible_in(&order)?;
        self.right.admissible_in(&order)?;
        self.product.admissible_in(&order)?;
        // P4: the recorded generator products are the products of the bases.
        let mut expected: Vec<OrderElement> = Vec::with_capacity(4);
        for left in &self.left.basis() {
            for right in &self.right.basis() {
                expected.push(order.multiply(left, right));
            }
        }
        for (index, want) in expected.iter().enumerate() {
            let got = self
                .generator_products
                .get(index)
                .ok_or(IdealCertificateError::GeneratorProductMismatch { index })?;
            if got != want {
                return Err(IdealCertificateError::GeneratorProductMismatch { index });
            }
        }
        if self.generator_products.len() != expected.len() {
            return Err(IdealCertificateError::GeneratorProductMismatch {
                index: expected.len(),
            });
        }
        // P5: norms are multiplicative. Checked BEFORE the Hermite comparison
        // on purpose: after P6 the product is pinned exactly, so no forgery
        // could ever reach this guard if it ran second, and a guard no forgery
        // can reach is not a guard. It is also the one check here that does
        // not go through `hermite_normal_form`, which the producer and the
        // checker share.
        if self.product.norm() != self.left.norm() * self.right.norm() {
            return Err(IdealCertificateError::ProductNormMismatch);
        }
        // P6: the Hermite form over those products (and their ω-multiples) is
        // the recorded product ideal.
        let recomputed = order
            .ideal_from_generators(&self.generator_products)
            .map_err(|_| IdealCertificateError::ProductHermiteMismatch)?;
        if recomputed != self.product {
            return Err(IdealCertificateError::ProductHermiteMismatch);
        }
        Ok(())
    }
}

impl QuadraticOrder {
    /// The product ideal `I·J`, with a certificate.
    ///
    /// # Errors
    ///
    /// [`IdealDecline::ZeroInput`] if the products span a rank-deficient
    /// module, which cannot happen for two admissible ideals and is reported
    /// rather than assumed away.
    pub fn multiply_ideals(
        &self,
        left: &Ideal,
        right: &Ideal,
    ) -> Result<(Ideal, IdealProductCertificate), IdealDecline> {
        let mut generator_products: Vec<OrderElement> = Vec::with_capacity(4);
        for x in &left.basis() {
            for y in &right.basis() {
                generator_products.push(self.multiply(x, y));
            }
        }
        let product = self.ideal_from_generators(&generator_products)?;
        let certificate = IdealProductCertificate {
            radicand: self.radicand.clone(),
            omega_trace: self.trace.clone(),
            omega_constant: self.constant.clone(),
            left: left.clone(),
            right: right.clone(),
            generator_products,
            product: product.clone(),
        };
        Ok((product, certificate))
    }

    /// `I^exponent`, by repeated multiplication. `uncertified` on its own; the
    /// certified route is the product certificate on each step, or the
    /// factorization certificate that consumes it.
    ///
    /// # Errors
    ///
    /// [`IdealDecline::ZeroInput`] from the underlying multiplication.
    pub fn ideal_power(&self, ideal: &Ideal, exponent: u32) -> Result<Ideal, IdealDecline> {
        let mut accumulator = self.unit_ideal();
        for _ in 0..exponent {
            accumulator = self.multiply_ideals(&accumulator, ideal)?.0;
        }
        Ok(accumulator)
    }
}

// ---------------------------------------------------------------------------
// How a rational prime splits
// ---------------------------------------------------------------------------

/// How a rational prime `p` decomposes in `O_K`.
///
/// The three cases are exactly the three values of the Kronecker symbol
/// `(D/p)`, which is what [`PrimeSplittingCertificate::verify`] recomputes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SplittingType {
    /// `(D/p) = 1`: `(p) = 𝔭·𝔭'` with `𝔭 ≠ 𝔭'`, both of norm `p`.
    Split,
    /// `(D/p) = −1`: `(p)` is itself prime, of norm `p²`.
    Inert,
    /// `(D/p) = 0`: `(p) = 𝔭²`, with `𝔭` of norm `p`.
    Ramified,
}

impl SplittingType {
    /// The Kronecker symbol this splitting type corresponds to.
    #[must_use]
    pub fn kronecker_value(self) -> i32 {
        match self {
            SplittingType::Split => 1,
            SplittingType::Inert => -1,
            SplittingType::Ramified => 0,
        }
    }

    /// How many prime ideals a certificate of this type must list, counted
    /// with multiplicity.
    #[must_use]
    pub fn factor_count(self) -> usize {
        match self {
            SplittingType::Split | SplittingType::Ramified => 2,
            SplittingType::Inert => 1,
        }
    }
}

impl fmt::Display for SplittingType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// The decomposition of a rational prime into prime ideals.
///
/// `verify` re-derives the splitting type from the Kronecker symbol `(D/p)`,
/// re-checks every listed ideal's norm, and multiplies the listed ideals back
/// together through [`IdealProductCertificate`] to confirm they give `(p)`.
/// It never consults the root of `x² − t·x − n mod p` the producer used.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimeSplittingCertificate {
    /// The squarefree radicand `d`.
    pub radicand: BigInt,
    /// `t` in `ω² = t·ω + n`.
    pub omega_trace: BigInt,
    /// `n` in `ω² = t·ω + n`.
    pub omega_constant: BigInt,
    /// The field discriminant `D`, recorded so a wrong one is refused rather
    /// than silently recomputed.
    pub discriminant: BigInt,
    /// The rational prime being decomposed.
    pub prime: BigInt,
    /// The claimed splitting type.
    pub splitting: SplittingType,
    /// The prime ideals above `p`, with multiplicity: two equal entries when
    /// ramified, two distinct when split, one when inert.
    pub factors: Vec<Ideal>,
}

/// Rebuild the order a certificate's recorded parameters describe.
fn order_from_parameters(
    radicand: &BigInt,
    trace: &BigInt,
    constant: &BigInt,
    discriminant: &BigInt,
) -> Result<QuadraticOrder, IdealCertificateError> {
    let order = QuadraticOrder::new(radicand)
        .map_err(|_| IdealCertificateError::OrderParametersMismatch)?;
    if order.omega_trace() != trace
        || order.omega_constant() != constant
        || order.discriminant() != discriminant
    {
        return Err(IdealCertificateError::OrderParametersMismatch);
    }
    Ok(order)
}

/// Multiply a list of ideals, each step re-checked by its own product
/// certificate, starting from `(1)`.
fn product_of_ideals(
    order: &QuadraticOrder,
    ideals: &[Ideal],
) -> Result<Ideal, IdealCertificateError> {
    let mut accumulator = order.unit_ideal();
    for ideal in ideals {
        let (next, certificate) = order
            .multiply_ideals(&accumulator, ideal)
            .map_err(|_| IdealCertificateError::ProductHermiteMismatch)?;
        certificate.verify()?;
        accumulator = next;
    }
    Ok(accumulator)
}

impl PrimeSplittingCertificate {
    /// Re-derive the whole decomposition from `(d, p)` alone.
    ///
    /// # Errors
    ///
    /// [`IdealCertificateError::OrderParametersMismatch`] for a wrong order;
    /// [`IdealCertificateError::MagnitudeOutOfRange`] when `p` or `D` is past
    /// the reused `i128` routines; [`IdealCertificateError::SplittingBaseNotPrime`]
    /// for a composite `p`; [`IdealCertificateError::SplittingTypeMismatch`]
    /// when `(D/p)` disagrees with the recorded type;
    /// [`IdealCertificateError::SplittingFactorCountMismatch`] and
    /// [`IdealCertificateError::SplittingFactorDistinctnessMismatch`] for a
    /// mis-shaped factor list; [`IdealCertificateError::PrimeIdealNormMismatch`]
    /// for a factor of the wrong norm; and
    /// [`IdealCertificateError::SplittingProductMismatch`] when the factors do
    /// not multiply back to `(p)`.
    pub fn verify(&self) -> Result<(), IdealCertificateError> {
        let order = order_from_parameters(
            &self.radicand,
            &self.omega_trace,
            &self.omega_constant,
            &self.discriminant,
        )?;
        // S1: p really is prime.
        let prime = to_i128(&self.prime).ok_or(IdealCertificateError::MagnitudeOutOfRange)?;
        if prime < 2 || !is_prime(prime) {
            return Err(IdealCertificateError::SplittingBaseNotPrime);
        }
        // S2: the splitting type is the one (D/p) says.
        let discriminant =
            to_i128(&self.discriminant).ok_or(IdealCertificateError::MagnitudeOutOfRange)?;
        let symbol = kronecker_symbol(discriminant, prime);
        if symbol != self.splitting.kronecker_value() {
            return Err(IdealCertificateError::SplittingTypeMismatch { symbol });
        }
        // S3: the right number of prime ideals for that type.
        let expected = self.splitting.factor_count();
        if self.factors.len() != expected {
            return Err(IdealCertificateError::SplittingFactorCountMismatch {
                found: self.factors.len(),
                expected,
            });
        }
        // S4: split means two different primes, ramified means the same one
        // twice. Without this a "split" listing 𝔭 twice would pass S3 and S5.
        match self.splitting {
            SplittingType::Split if self.factors[0] == self.factors[1] => {
                return Err(IdealCertificateError::SplittingFactorDistinctnessMismatch);
            }
            SplittingType::Ramified if self.factors[0] != self.factors[1] => {
                return Err(IdealCertificateError::SplittingFactorDistinctnessMismatch);
            }
            _ => {}
        }
        // S5: the factors multiply back to (p). This runs BEFORE the norm
        // check because an ideal of norm p is *forced* to be one of the primes
        // above p — so with the norms already pinned no forgery could reach
        // this guard, and a guard no forgery can reach is not a guard.
        let product = product_of_ideals(&order, &self.factors)?;
        let principal = order
            .rational_ideal(&self.prime)
            .map_err(|_| IdealCertificateError::SplittingProductMismatch)?;
        if product != principal {
            return Err(IdealCertificateError::SplittingProductMismatch);
        }
        // S6: each factor has the norm its splitting type forces.
        let wanted_norm = match self.splitting {
            SplittingType::Inert => &self.prime * &self.prime,
            SplittingType::Split | SplittingType::Ramified => self.prime.clone(),
        };
        for (index, factor) in self.factors.iter().enumerate() {
            if factor.norm() != wanted_norm {
                return Err(IdealCertificateError::PrimeIdealNormMismatch { index });
            }
        }
        Ok(())
    }
}

impl QuadraticOrder {
    /// The roots of `x² − t·x − n` modulo `p`, ascending.
    ///
    /// The minimal polynomial of `ω` is `x² − t·x − n`, so Dedekind's
    /// criterion reads the splitting of `p` straight off this factorization.
    fn omega_roots_mod(&self, prime: i128) -> Result<Vec<i128>, IdealDecline> {
        let trace = to_i128(&self.trace).ok_or(IdealDecline::MagnitudeOutOfRange)?;
        let constant = to_i128(&self.constant).ok_or(IdealDecline::MagnitudeOutOfRange)?;
        if prime == 2 {
            // Two candidates; brute force beats a special case in the general
            // formula, which divides by 2.
            let mut roots = Vec::new();
            for candidate in [0i128, 1] {
                let value = (candidate * candidate - trace * candidate - constant).rem_euclid(2);
                if value == 0 {
                    roots.push(candidate);
                }
            }
            return Ok(roots);
        }
        let discriminant = to_i128(&self.discriminant).ok_or(IdealDecline::MagnitudeOutOfRange)?;
        let residue = discriminant.rem_euclid(prime);
        let inverse_two = (prime + 1) / 2; // 2·((p+1)/2) ≡ 1 (mod p) for odd p
        if residue == 0 {
            let root = (trace.rem_euclid(prime) * inverse_two).rem_euclid(prime);
            return Ok(vec![root]);
        }
        match sqrt_mod(residue, prime) {
            None if kronecker_symbol(discriminant, prime) == -1 => Ok(Vec::new()),
            None => Err(IdealDecline::SqrtModDeclined { prime }),
            Some(root) => {
                let trace_residue = trace.rem_euclid(prime);
                let plus = ((trace_residue + root) * inverse_two).rem_euclid(prime);
                let minus =
                    ((trace_residue - root).rem_euclid(prime) * inverse_two).rem_euclid(prime);
                let mut roots = vec![plus.min(minus), plus.max(minus)];
                roots.dedup();
                Ok(roots)
            }
        }
    }

    /// The prime ideal `𝔭 = (p, ω − r)` for a root `r` of `x² − t·x − n mod p`.
    fn prime_above(&self, prime: &BigInt, root: i128) -> Result<Ideal, IdealDecline> {
        let generators = [
            OrderElement::new(prime.clone(), big_zero()),
            OrderElement::new(-BigInt::from(root), big_one()),
        ];
        self.ideal_from_generators(&generators)
    }

    /// Decompose the rational prime `p` into prime ideals, with a certificate.
    ///
    /// The route is Dedekind's: factor the minimal polynomial `x² − t·x − n`
    /// of `ω` modulo `p`. Two roots give a split, one root a ramification, and
    /// none an inert prime — and that trichotomy is exactly `(D/p) = 1, 0, −1`,
    /// which the certificate recomputes independently.
    ///
    /// # Errors
    ///
    /// [`IdealDecline::MagnitudeOutOfRange`] past the `i128` routines,
    /// [`IdealDecline::NotPrime`] for a composite argument,
    /// [`IdealDecline::SqrtModDeclined`] if Tonelli–Shanks declines, and
    /// [`IdealDecline::ZeroInput`] from a degenerate Hermite form.
    pub fn split_prime(
        &self,
        prime: &BigInt,
    ) -> Result<(Vec<Ideal>, PrimeSplittingCertificate), IdealDecline> {
        let small = to_i128(prime).ok_or(IdealDecline::MagnitudeOutOfRange)?;
        if small < 2 || !is_prime(small) {
            return Err(IdealDecline::NotPrime);
        }
        let roots = self.omega_roots_mod(small)?;
        let (splitting, factors) = match roots.len() {
            0 => (SplittingType::Inert, vec![self.rational_ideal(prime)?]),
            1 => {
                let ideal = self.prime_above(prime, roots[0])?;
                (SplittingType::Ramified, vec![ideal.clone(), ideal])
            }
            _ => {
                let mut ideals = vec![
                    self.prime_above(prime, roots[0])?,
                    self.prime_above(prime, roots[1])?,
                ];
                ideals.sort();
                (SplittingType::Split, ideals)
            }
        };
        let certificate = PrimeSplittingCertificate {
            radicand: self.radicand.clone(),
            omega_trace: self.trace.clone(),
            omega_constant: self.constant.clone(),
            discriminant: self.discriminant.clone(),
            prime: prime.clone(),
            splitting,
            factors: factors.clone(),
        };
        Ok((factors, certificate))
    }

    /// The distinct prime ideals above `p`, ascending.
    fn distinct_primes_above(&self, prime: &BigInt) -> Result<Vec<Ideal>, IdealDecline> {
        let (mut factors, _) = self.split_prime(prime)?;
        factors.sort();
        factors.dedup();
        Ok(factors)
    }
}

// ---------------------------------------------------------------------------
// Factoring an ideal into prime ideals
// ---------------------------------------------------------------------------

/// `I = ∏ 𝔭ᵢ^{eᵢ}`.
///
/// `verify` re-derives the prime ideals above each factor's norm, checks the
/// listed factor is one of them, and multiplies the whole product back out
/// through [`IdealProductCertificate`]. The exponents the producer found by
/// containment tests are never trusted — only the product identity is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdealFactorizationCertificate {
    /// The squarefree radicand `d`.
    pub radicand: BigInt,
    /// `t` in `ω² = t·ω + n`.
    pub omega_trace: BigInt,
    /// `n` in `ω² = t·ω + n`.
    pub omega_constant: BigInt,
    /// The field discriminant `D`.
    pub discriminant: BigInt,
    /// The ideal being factored.
    pub ideal: Ideal,
    /// The prime ideals and their exponents, ascending by ideal.
    pub factors: Vec<(Ideal, u32)>,
}

impl IdealFactorizationCertificate {
    /// Re-derive `I = ∏ 𝔭ᵢ^{eᵢ}` from the recorded data alone.
    ///
    /// # Errors
    ///
    /// [`IdealCertificateError::OrderParametersMismatch`],
    /// [`IdealCertificateError::ZeroExponent`],
    /// [`IdealCertificateError::FactorNormNotAPrimePower`],
    /// [`IdealCertificateError::FactorIsNotAPrimeIdeal`],
    /// [`IdealCertificateError::FactorizationProductMismatch`] and
    /// [`IdealCertificateError::FactorizationNormMismatch`], plus the
    /// [`Ideal::admissible_in`] refusals.
    pub fn verify(&self) -> Result<(), IdealCertificateError> {
        let order = order_from_parameters(
            &self.radicand,
            &self.omega_trace,
            &self.omega_constant,
            &self.discriminant,
        )?;
        // F1: the target really is an ideal of this order.
        self.ideal.admissible_in(&order)?;
        let mut product = order.unit_ideal();
        let mut norm = big_one();
        for (index, (factor, exponent)) in self.factors.iter().enumerate() {
            // F2: an exponent of zero asserts nothing and would let a factor
            // list name arbitrary ideals.
            if *exponent == 0 {
                return Err(IdealCertificateError::ZeroExponent { index });
            }
            factor.admissible_in(&order)?;
            // F3: the factor is one of the prime ideals above its own norm's
            // rational prime.
            Self::check_is_prime_ideal(&order, factor, index)?;
            // F4: accumulate the product and the norm independently.
            for _ in 0..*exponent {
                let (next, certificate) = order
                    .multiply_ideals(&product, factor)
                    .map_err(|_| IdealCertificateError::FactorizationProductMismatch)?;
                certificate.verify()?;
                product = next;
                norm *= factor.norm();
            }
        }
        // F5: norms are multiplicative. Before the product comparison for the
        // same reason as in [`IdealProductCertificate::verify`]: F6 pins the
        // product exactly, so running the norm check second would make it
        // unreachable by any forgery.
        if norm != self.ideal.norm() {
            return Err(IdealCertificateError::FactorizationNormMismatch);
        }
        // F6: the product is the target.
        if product != self.ideal {
            return Err(IdealCertificateError::FactorizationProductMismatch);
        }
        Ok(())
    }

    /// One listed factor is a prime ideal: its norm is `p` or `p²` for a
    /// rational prime `p`, and it appears among the primes above that `p`.
    fn check_is_prime_ideal(
        order: &QuadraticOrder,
        factor: &Ideal,
        index: usize,
    ) -> Result<(), IdealCertificateError> {
        let norm = to_i128(&factor.norm()).ok_or(IdealCertificateError::MagnitudeOutOfRange)?;
        let base = if is_prime(norm) {
            norm
        } else {
            let root = norm.isqrt();
            if root * root != norm || !is_prime(root) {
                return Err(IdealCertificateError::FactorNormNotAPrimePower { index });
            }
            root
        };
        let (primes, certificate) = order
            .split_prime(&BigInt::from(base))
            .map_err(|_| IdealCertificateError::FactorIsNotAPrimeIdeal { index })?;
        certificate.verify()?;
        if primes.contains(factor) {
            Ok(())
        } else {
            Err(IdealCertificateError::FactorIsNotAPrimeIdeal { index })
        }
    }
}

impl QuadraticOrder {
    /// Factor a nonzero ideal into prime ideals.
    ///
    /// The route is: factor `N(I)` over ℤ with the crate's own
    /// [`crate::ntheory::factorize`], take the prime ideals above each rational
    /// prime with [`QuadraticOrder::split_prime`], and read each exponent off
    /// by containment. The exponent search is a heuristic that the
    /// certificate's product identity makes safe — a wrong exponent cannot
    /// survive `verify`, and a search that falls short is reported as
    /// [`IdealDecline::FactorizationIncomplete`] rather than shipped.
    ///
    /// # Errors
    ///
    /// [`IdealDecline::MagnitudeOutOfRange`] when `N(I)` is past the `i128`
    /// factorizer, and the [`QuadraticOrder::split_prime`] declines.
    pub fn factor_ideal(
        &self,
        ideal: &Ideal,
    ) -> Result<IdealFactorizationCertificate, IdealDecline> {
        let norm = ideal.norm();
        let small = to_i128(&norm).ok_or(IdealDecline::MagnitudeOutOfRange)?;
        if small <= 0 {
            return Err(IdealDecline::ZeroInput);
        }
        let mut factors: BTreeMap<Ideal, u32> = BTreeMap::new();
        for (prime, multiplicity) in factorize(small) {
            let big_prime = BigInt::from(prime);
            for candidate in self.distinct_primes_above(&big_prime)? {
                let exponent = self.valuation(ideal, &candidate, multiplicity)?;
                if exponent > 0 {
                    factors.insert(candidate, exponent);
                }
            }
        }
        let factors: Vec<(Ideal, u32)> = factors.into_iter().collect();
        let certificate = IdealFactorizationCertificate {
            radicand: self.radicand.clone(),
            omega_trace: self.trace.clone(),
            omega_constant: self.constant.clone(),
            discriminant: self.discriminant.clone(),
            ideal: ideal.clone(),
            factors,
        };
        if certificate.verify().is_err() {
            return Err(IdealDecline::FactorizationIncomplete);
        }
        Ok(certificate)
    }

    /// The largest `e ≤ bound` with `I ⊆ 𝔭^e`.
    fn valuation(
        &self,
        ideal: &Ideal,
        prime_ideal: &Ideal,
        bound: u32,
    ) -> Result<u32, IdealDecline> {
        let mut power = self.unit_ideal();
        let mut exponent = 0u32;
        for _ in 0..bound {
            let next = self.multiply_ideals(&power, prime_ideal)?.0;
            if !next.contains(ideal) {
                break;
            }
            power = next;
            exponent += 1;
        }
        Ok(exponent)
    }

    /// Factor the principal ideal `(α)` into prime ideals.
    ///
    /// # Errors
    ///
    /// [`IdealDecline::ZeroInput`] for `α = 0`, plus the
    /// [`QuadraticOrder::factor_ideal`] declines.
    pub fn factor_principal_ideal(
        &self,
        element: &OrderElement,
    ) -> Result<(Ideal, IdealFactorizationCertificate), IdealDecline> {
        if element.is_zero() {
            return Err(IdealDecline::ZeroInput);
        }
        let ideal = self.principal_ideal(element)?;
        let certificate = self.factor_ideal(&ideal)?;
        Ok((ideal, certificate))
    }
}

// ---------------------------------------------------------------------------
// The class group of an imaginary quadratic field, by reduced forms
// ---------------------------------------------------------------------------

/// The integral binary quadratic form `a·x² + b·x·y + c·y²`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct BinaryQuadraticForm {
    a: BigInt,
    b: BigInt,
    c: BigInt,
}

impl BinaryQuadraticForm {
    /// The form `a·x² + b·x·y + c·y²`.
    #[must_use]
    pub fn new(a: BigInt, b: BigInt, c: BigInt) -> BinaryQuadraticForm {
        BinaryQuadraticForm { a, b, c }
    }

    /// The form `a·x² + b·x·y + c·y²`, from machine integers.
    #[must_use]
    pub fn from_i64(a: i64, b: i64, c: i64) -> BinaryQuadraticForm {
        BinaryQuadraticForm::new(BigInt::from(a), BigInt::from(b), BigInt::from(c))
    }

    /// The three coefficients `(a, b, c)`.
    #[must_use]
    pub fn coefficients(&self) -> (&BigInt, &BigInt, &BigInt) {
        (&self.a, &self.b, &self.c)
    }

    /// The discriminant `b² − 4ac`.
    #[must_use]
    pub fn discriminant(&self) -> BigInt {
        &self.b * &self.b - 4u32 * &self.a * &self.c
    }

    /// `gcd(a, b, c) = 1`. An imprimitive form is a scalar multiple of a form
    /// of smaller discriminant and does not count towards `h(D)`.
    #[must_use]
    pub fn is_primitive(&self) -> bool {
        big_gcd(&big_gcd(&self.a, &self.b), &self.c).is_one()
    }

    /// `a > 0`, which for `D < 0` is exactly positive definiteness.
    #[must_use]
    pub fn is_positive_definite(&self) -> bool {
        self.a.is_positive()
    }

    /// The reduction condition `|b| ≤ a ≤ c`, with `b ≥ 0` whenever `|b| = a`
    /// or `a = c`.
    ///
    /// The boundary convention is what makes the reduced form in each class
    /// unique: `(a, −b, c)` and `(a, b, c)` are equivalent when `|b| = a` or
    /// `a = c`, so exactly one of the two is kept.
    #[must_use]
    pub fn is_reduced(&self) -> bool {
        let magnitude = self.b.abs();
        if magnitude > self.a || self.a > self.c {
            return false;
        }
        if (magnitude == self.a || self.a == self.c) && self.b.is_negative() {
            return false;
        }
        true
    }
}

impl fmt::Display for BinaryQuadraticForm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {}, {})", self.a, self.b, self.c)
    }
}

/// The full list of reduced positive definite primitive forms of a negative
/// discriminant, which is the class group of `O_K` as a set.
///
/// **The theorem this rests on.** *Every positive definite primitive integral
/// binary quadratic form of discriminant `D < 0` is `SL₂(ℤ)`-equivalent to
/// exactly one reduced form.* Its hypothesis is `D < 0` and `D ≡ 0` or
/// `1 (mod 4)`, both of which `verify` checks. Uniqueness is what turns
/// "these forms are pairwise different" into "these classes are pairwise
/// different", so no composition or explicit equivalence test is needed — and
/// none is shipped.
///
/// `verify` re-derives every listed form's discriminant, primitivity,
/// definiteness and reducedness, checks the list has no repeats, and then
/// **recounts the whole reduced region with a different traversal** than the
/// producer used: the producer loops over `b` and divisors of `(b² − D)/4`,
/// the checker loops over `a` and then `b`. A list missing a form fails the
/// recount; a list with an extra form fails one of the per-form checks or the
/// recount.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassNumberCertificate {
    /// The discriminant `D < 0`.
    pub discriminant: BigInt,
    /// Every reduced form of that discriminant, ascending.
    pub forms: Vec<BinaryQuadraticForm>,
}

impl ClassNumberCertificate {
    /// The class number `h(D)`, which is the number of listed forms.
    #[must_use]
    pub fn class_number(&self) -> usize {
        self.forms.len()
    }

    /// Re-derive the whole list from `D` alone.
    ///
    /// # Errors
    ///
    /// [`IdealCertificateError::DiscriminantNotNegative`] and
    /// [`IdealCertificateError::DiscriminantNotAdmissible`] for a `D` outside
    /// the theorem's hypothesis; [`IdealCertificateError::FormDiscriminantMismatch`],
    /// [`IdealCertificateError::FormNotPositiveDefinite`],
    /// [`IdealCertificateError::FormNotPrimitive`] and
    /// [`IdealCertificateError::FormNotReduced`] naming the offending form;
    /// [`IdealCertificateError::FormsNotDistinct`] for a repeat; and
    /// [`IdealCertificateError::ClassNumberRecountMismatch`] when the
    /// checker's own enumeration disagrees.
    pub fn verify(&self) -> Result<(), IdealCertificateError> {
        // C1: D < 0 — the hypothesis of the uniqueness theorem.
        if !self.discriminant.is_negative() {
            return Err(IdealCertificateError::DiscriminantNotNegative);
        }
        // C2: D ≡ 0 or 1 (mod 4), or no integral form has this discriminant.
        let residue = big_mod_positive(&self.discriminant, &BigInt::from(4));
        if !(residue.is_zero() || residue.is_one()) {
            return Err(IdealCertificateError::DiscriminantNotAdmissible);
        }
        let mut seen: BTreeSet<BinaryQuadraticForm> = BTreeSet::new();
        for (index, form) in self.forms.iter().enumerate() {
            // C3: the form has this discriminant.
            if form.discriminant() != self.discriminant {
                return Err(IdealCertificateError::FormDiscriminantMismatch { index });
            }
            // C4: positive definite.
            if !form.is_positive_definite() {
                return Err(IdealCertificateError::FormNotPositiveDefinite { index });
            }
            // C5: primitive.
            if !form.is_primitive() {
                return Err(IdealCertificateError::FormNotPrimitive { index });
            }
            // C6: reduced, recomputed rather than taken on trust.
            if !form.is_reduced() {
                return Err(IdealCertificateError::FormNotReduced { index });
            }
            // C7: no repeats. With C6 and the uniqueness theorem, distinct
            // reduced forms are inequivalent, so this is what makes the count
            // a count of *classes*.
            if !seen.insert(form.clone()) {
                return Err(IdealCertificateError::FormsNotDistinct { index });
            }
        }
        // C8: completeness, by an independent traversal of the same region.
        let recounted = count_reduced_forms_by_leading(&self.discriminant);
        if recounted != self.forms.len() {
            return Err(IdealCertificateError::ClassNumberRecountMismatch {
                claimed: self.forms.len(),
                recounted,
            });
        }
        Ok(())
    }
}

/// `|b| ≤ a ≤ c` and `4ac = b² − D` force `3a² ≤ |D|` and `3b² ≤ |D|`, so both
/// coefficients are bounded by `⌊√(⌊|D|/3⌋)⌋`.
fn reduced_coefficient_bound(discriminant: &BigInt) -> BigInt {
    big_isqrt(&(discriminant.abs() / 3u32))
}

/// The producer's traversal: over `b`, then over the divisors `a` of
/// `(b² − D)/4` with `a ≤ √((b² − D)/4)`.
fn enumerate_reduced_forms(discriminant: &BigInt) -> Vec<BinaryQuadraticForm> {
    let bound = reduced_coefficient_bound(discriminant);
    let mut forms: BTreeSet<BinaryQuadraticForm> = BTreeSet::new();
    let mut b = -bound.clone();
    while b <= bound {
        let numerator = &b * &b - discriminant;
        if (&numerator % 4u32).is_zero() {
            let product = numerator / 4u32;
            collect_forms_for_off_diagonal(&b, &product, &mut forms);
        }
        b += 1u32;
    }
    forms.into_iter().collect()
}

/// Every reduced form with this `b` and `a·c = product`.
fn collect_forms_for_off_diagonal(
    b: &BigInt,
    product: &BigInt,
    forms: &mut BTreeSet<BinaryQuadraticForm>,
) {
    if !product.is_positive() {
        return;
    }
    let limit = big_isqrt(product);
    let mut a = b.abs().max(big_one());
    while a <= limit {
        if (product % &a).is_zero() {
            let c = product / &a;
            let form = BinaryQuadraticForm::new(a.clone(), b.clone(), c);
            if form.is_primitive() && form.is_reduced() {
                forms.insert(form);
            }
        }
        a += 1u32;
    }
}

/// The checker's traversal: over `a`, then over `b` in `−a ..= a`, solving for
/// `c` directly. Deliberately a different loop order from
/// [`enumerate_reduced_forms`], so a bug in one is not a bug in both.
fn count_reduced_forms_by_leading(discriminant: &BigInt) -> usize {
    let bound = reduced_coefficient_bound(discriminant);
    let mut count = 0usize;
    let mut a = big_one();
    while a <= bound {
        let mut b = -a.clone();
        while b <= a {
            let numerator = &b * &b - discriminant;
            let divisor = 4u32 * &a;
            if (&numerator % &divisor).is_zero() {
                let c = numerator / &divisor;
                let form = BinaryQuadraticForm::new(a.clone(), b.clone(), c);
                if form.is_primitive() && form.is_reduced() {
                    count += 1;
                }
            }
            b += 1u32;
        }
        a += 1u32;
    }
    count
}

/// The class number `h(D)` of an imaginary quadratic order, with the full list
/// of reduced forms as its certificate.
///
/// # Errors
///
/// [`IdealDecline::DiscriminantNotNegative`] for `D ≥ 0` — real quadratic
/// class numbers are out of scope, see the module documentation;
/// [`IdealDecline::DiscriminantNotAdmissible`] for `D ≢ 0, 1 (mod 4)`; and
/// [`IdealDecline::DiscriminantTooLarge`] above
/// [`CLASS_NUMBER_DISCRIMINANT_BOUND`].
pub fn class_number(
    discriminant: &BigInt,
) -> Result<(usize, ClassNumberCertificate), IdealDecline> {
    if !discriminant.is_negative() {
        return Err(IdealDecline::DiscriminantNotNegative);
    }
    let residue = big_mod_positive(discriminant, &BigInt::from(4));
    if !(residue.is_zero() || residue.is_one()) {
        return Err(IdealDecline::DiscriminantNotAdmissible);
    }
    if discriminant.abs() > BigInt::from(CLASS_NUMBER_DISCRIMINANT_BOUND) {
        return Err(IdealDecline::DiscriminantTooLarge {
            bound: CLASS_NUMBER_DISCRIMINANT_BOUND,
        });
    }
    let forms = enumerate_reduced_forms(discriminant);
    let certificate = ClassNumberCertificate {
        discriminant: discriminant.clone(),
        forms,
    };
    Ok((certificate.class_number(), certificate))
}

impl QuadraticOrder {
    /// The class number of this order, when it is imaginary quadratic.
    ///
    /// # Errors
    ///
    /// The [`class_number`] declines, including
    /// [`IdealDecline::DiscriminantNotNegative`] for a real quadratic field.
    pub fn class_number(&self) -> Result<(usize, ClassNumberCertificate), IdealDecline> {
        class_number(&self.discriminant)
    }
}

// ---------------------------------------------------------------------------
// A primitive element for a compositum
// ---------------------------------------------------------------------------

/// The Sylvester resultant of two least-significant-first `ℚ[x]` vectors.
///
/// Both must be non-constant. The determinant is the one already in
/// `numberfield.rs`, reused rather than re-derived.
fn poly_resultant(left: &[BigRational], right: &[BigRational]) -> Option<BigRational> {
    let left_degree = poly_degree(left)?;
    let right_degree = poly_degree(right)?;
    if left_degree == 0 || right_degree == 0 {
        return None;
    }
    let size = left_degree + right_degree;
    let mut matrix = vec![vec![rat_zero(); size]; size];
    for row in 0..right_degree {
        for offset in 0..=left_degree {
            matrix[row][row + offset] = left[left_degree - offset].clone();
        }
    }
    for row in 0..left_degree {
        for offset in 0..=right_degree {
            matrix[right_degree + row][row + offset] = right[right_degree - offset].clone();
        }
    }
    Some(matrix_determinant(&matrix))
}

/// `poly(constant + slope·y)`, by Horner over the linear substitution.
fn poly_compose_linear(
    poly: &[BigRational],
    constant: &BigRational,
    slope: &BigRational,
) -> Vec<BigRational> {
    let linear = vec![constant.clone(), slope.clone()];
    let mut accumulator: Vec<BigRational> = Vec::new();
    for coefficient in poly.iter().rev() {
        accumulator = poly_add(
            &poly_mul(&accumulator, &linear),
            core::slice::from_ref(coefficient),
        );
    }
    poly_trim(accumulator)
}

/// Lagrange interpolation through distinct abscissae.
fn lagrange_interpolate(points: &[(BigRational, BigRational)]) -> Vec<BigRational> {
    let mut result: Vec<BigRational> = Vec::new();
    for (index, (abscissa, ordinate)) in points.iter().enumerate() {
        let mut basis = vec![rat_one()];
        let mut denominator = rat_one();
        for (other, (node, _)) in points.iter().enumerate() {
            if other == index {
                continue;
            }
            basis = poly_mul(&basis, &[-node.clone(), rat_one()]);
            denominator *= abscissa - node;
        }
        let scale = ordinate / denominator;
        result = poly_add(&result, &poly_scale(&basis, &scale));
    }
    poly_trim(result)
}

/// `Res_y(f(θ − k·y), g(y))` as a polynomial in `θ`.
///
/// Computed by evaluation and interpolation rather than a bivariate Sylvester
/// determinant: the resultant has degree exactly `deg f · deg g` in `θ`, and
/// the leading coefficient of `f(θ − k·y)` in `y` is the constant `(−k)^{deg f}`,
/// so no evaluation can drop the degree and `deg f · deg g + 1` points
/// determine it.
fn compositum_resultant(
    first: &[BigRational],
    second: &[BigRational],
    multiplier: &BigRational,
) -> Option<Vec<BigRational>> {
    let first_degree = poly_degree(first)?;
    let second_degree = poly_degree(second)?;
    let degree = first_degree * second_degree;
    let slope = -multiplier.clone();
    let mut points = Vec::with_capacity(degree + 1);
    for node in 0..=degree {
        let abscissa = BigRational::from_integer(BigInt::from(node));
        let shifted = poly_compose_linear(first, &abscissa, &slope);
        let value = poly_resultant(&shifted, second)?;
        points.push((abscissa, value));
    }
    Some(lagrange_interpolate(&points))
}

/// Whether a non-constant `ℚ[x]` polynomial has no repeated root, i.e.
/// `gcd(p, p′)` is a nonzero constant.
fn poly_is_squarefree(poly: &[BigRational]) -> bool {
    let Some(degree) = poly_degree(poly) else {
        return false;
    };
    if degree == 0 {
        return false;
    }
    let derivative: Vec<BigRational> = poly
        .iter()
        .enumerate()
        .skip(1)
        .map(|(index, coefficient)| coefficient * BigRational::from_integer(BigInt::from(index)))
        .collect();
    let (gcd, _, _) = poly_ext_gcd(poly, &poly_trim(derivative));
    poly_degree(&gcd) == Some(0)
}

// --- polynomials over the compositum ---------------------------------------

fn kpoly_trim(mut poly: Vec<Element>) -> Vec<Element> {
    while poly.last().is_some_and(Element::is_zero) {
        poly.pop();
    }
    poly
}

fn kpoly_degree(poly: &[Element]) -> Option<usize> {
    let trimmed = kpoly_trim(poly.to_vec());
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.len() - 1)
    }
}

fn kpoly_mul(field: &NumberField, left: &[Element], right: &[Element]) -> Option<Vec<Element>> {
    if left.is_empty() || right.is_empty() {
        return Some(Vec::new());
    }
    let mut out = vec![field.zero(); left.len() + right.len() - 1];
    for (i, a) in left.iter().enumerate() {
        for (j, b) in right.iter().enumerate() {
            let term = a.mul(b)?;
            out[i + j] = out[i + j].add(&term)?;
        }
    }
    Some(kpoly_trim(out))
}

/// The remainder of `dividend` on division by `divisor` in `K[y]`.
fn kpoly_rem(dividend: &[Element], divisor: &[Element]) -> Option<Vec<Element>> {
    let divisor_degree = kpoly_degree(divisor)?;
    let (lead_inverse, _) = divisor[divisor_degree].inverse()?;
    let mut remainder = kpoly_trim(dividend.to_vec());
    while let Some(remainder_degree) = kpoly_degree(&remainder) {
        if remainder_degree < divisor_degree {
            break;
        }
        let factor = remainder[remainder_degree].mul(&lead_inverse)?;
        let shift = remainder_degree - divisor_degree;
        for offset in 0..=divisor_degree {
            let term = factor.mul(&divisor[offset])?;
            remainder[shift + offset] = remainder[shift + offset].sub(&term)?;
        }
        remainder = kpoly_trim(remainder);
        if kpoly_degree(&remainder) == Some(remainder_degree) {
            return None; // the leading term did not cancel; refuse to loop
        }
    }
    Some(remainder)
}

/// The monic greatest common divisor in `K[y]`.
fn kpoly_gcd(left: &[Element], right: &[Element]) -> Option<Vec<Element>> {
    let mut previous = kpoly_trim(left.to_vec());
    let mut current = kpoly_trim(right.to_vec());
    while kpoly_degree(&current).is_some() {
        let remainder = kpoly_rem(&previous, &current)?;
        previous = core::mem::replace(&mut current, remainder);
    }
    let degree = kpoly_degree(&previous)?;
    let (inverse, _) = previous[degree].inverse()?;
    previous
        .iter()
        .map(|coefficient| coefficient.mul(&inverse))
        .collect()
}

/// `f(θ − k·y)` as a polynomial in `y` with coefficients in `K = ℚ(θ)`.
fn lift_shifted(
    field: &NumberField,
    poly: &[BigRational],
    multiplier: &BigRational,
) -> Option<Vec<Element>> {
    let linear = vec![field.generator(), field.rational(&-multiplier.clone())];
    let mut accumulator: Vec<Element> = Vec::new();
    for coefficient in poly.iter().rev() {
        let scaled = kpoly_mul(field, &accumulator, &linear)?;
        accumulator = kpoly_add(field, &scaled, &[field.rational(coefficient)])?;
    }
    Some(kpoly_trim(accumulator))
}

fn kpoly_add(field: &NumberField, left: &[Element], right: &[Element]) -> Option<Vec<Element>> {
    let mut out = vec![field.zero(); left.len().max(right.len())];
    for (index, value) in left.iter().enumerate() {
        out[index] = out[index].add(value)?;
    }
    for (index, value) in right.iter().enumerate() {
        out[index] = out[index].add(value)?;
    }
    Some(kpoly_trim(out))
}

/// Evaluate a `ℚ[x]` polynomial at an element of `K`, by Horner.
fn evaluate_in_field(field: &NumberField, poly: &[BigRational], at: &Element) -> Option<Element> {
    let mut accumulator = field.zero();
    for coefficient in poly.iter().rev() {
        accumulator = accumulator.mul(at)?.add(&field.rational(coefficient))?;
    }
    Some(accumulator)
}

/// `θ = α + k·β` generates `ℚ(α, β)`, with `α` and `β` written back as
/// polynomials in `θ`.
///
/// `verify` re-derives everything from `(f, g, k, R)`: that `R` is monic of
/// degree `deg f · deg g`, squarefree and irreducible over ℚ — so `ℚ[x]/(R)`
/// is a field of that degree — and then, **inside that field**, that the
/// recorded expression for `α` satisfies `f`, the one for `β` satisfies `g`,
/// and the two combine to `θ`. Those four facts together give
/// `ℚ(α, β) ⊆ ℚ(θ)` and `[ℚ(θ) : ℚ] = deg f · deg g`, which is the claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimitiveElementCertificate {
    /// The monic minimal polynomial `f` of `α`, least-significant-first.
    pub first_minpoly: Vec<BigRational>,
    /// The monic minimal polynomial `g` of `β`, least-significant-first.
    pub second_minpoly: Vec<BigRational>,
    /// The multiplier `k` in `θ = α + k·β`.
    pub multiplier: BigInt,
    /// The monic minimal polynomial of `θ`, least-significant-first.
    pub theta_minpoly: Vec<BigRational>,
    /// `α` as a polynomial in `θ`, least-significant-first.
    pub first_in_theta: Vec<BigRational>,
    /// `β` as a polynomial in `θ`, least-significant-first.
    pub second_in_theta: Vec<BigRational>,
}

impl PrimitiveElementCertificate {
    /// The degree `[ℚ(α, β) : ℚ]` the certificate claims.
    #[must_use]
    pub fn degree(&self) -> usize {
        poly_degree(&self.theta_minpoly).unwrap_or(0)
    }

    /// Re-derive the whole claim from the recorded polynomials alone.
    ///
    /// # Errors
    ///
    /// [`IdealCertificateError::GeneratorPolynomialNotMonic`],
    /// [`IdealCertificateError::PrimitiveElementMultiplierZero`],
    /// [`IdealCertificateError::CompositumDegreeMismatch`],
    /// [`IdealCertificateError::CompositumNotSquarefree`],
    /// [`IdealCertificateError::CompositumNotIrreducible`],
    /// [`IdealCertificateError::AlphaDoesNotSatisfyF`],
    /// [`IdealCertificateError::BetaDoesNotSatisfyG`], and
    /// [`IdealCertificateError::PrimitiveElementRelationFails`].
    pub fn verify(&self) -> Result<(), IdealCertificateError> {
        // E1: both generators are given by monic non-constant polynomials.
        let first_degree = monic_degree(&self.first_minpoly)
            .ok_or(IdealCertificateError::GeneratorPolynomialNotMonic)?;
        let second_degree = monic_degree(&self.second_minpoly)
            .ok_or(IdealCertificateError::GeneratorPolynomialNotMonic)?;
        // E2: k = 0 would make θ = α, which generates only ℚ(α).
        if self.multiplier.is_zero() {
            return Err(IdealCertificateError::PrimitiveElementMultiplierZero);
        }
        // E3: R is monic of the full degree deg f · deg g.
        let expected = first_degree * second_degree;
        let theta_degree = monic_degree(&self.theta_minpoly).ok_or(
            IdealCertificateError::CompositumDegreeMismatch {
                found: poly_degree(&self.theta_minpoly).unwrap_or(0),
                expected,
            },
        )?;
        if theta_degree != expected {
            return Err(IdealCertificateError::CompositumDegreeMismatch {
                found: theta_degree,
                expected,
            });
        }
        // E4: R is squarefree, so θ really has that degree rather than a
        // repeated-root polynomial merely annihilating it.
        if !poly_is_squarefree(&self.theta_minpoly) {
            return Err(IdealCertificateError::CompositumNotSquarefree);
        }
        // E5: ℚ[x]/(R) is a field. NumberField::new decides irreducibility
        // through the crate's own factorizer and never assumes it.
        let field = NumberField::new(&self.theta_minpoly)
            .map_err(|_| IdealCertificateError::CompositumNotIrreducible)?;
        let alpha = field.element(&self.first_in_theta);
        let beta = field.element(&self.second_in_theta);
        // E6: the recorded α satisfies f inside that field.
        let value = evaluate_in_field(&field, &self.first_minpoly, &alpha)
            .ok_or(IdealCertificateError::AlphaDoesNotSatisfyF)?;
        if !value.is_zero() {
            return Err(IdealCertificateError::AlphaDoesNotSatisfyF);
        }
        // E7: the recorded β satisfies g.
        let value = evaluate_in_field(&field, &self.second_minpoly, &beta)
            .ok_or(IdealCertificateError::BetaDoesNotSatisfyG)?;
        if !value.is_zero() {
            return Err(IdealCertificateError::BetaDoesNotSatisfyG);
        }
        // E8: α + k·β is θ itself.
        let multiplier = BigRational::from_integer(self.multiplier.clone());
        let combination = alpha
            .add(&beta.scale(&multiplier))
            .ok_or(IdealCertificateError::PrimitiveElementRelationFails)?;
        if combination != field.generator() {
            return Err(IdealCertificateError::PrimitiveElementRelationFails);
        }
        Ok(())
    }
}

/// The degree of a monic non-constant polynomial, or `None`.
fn monic_degree(poly: &[BigRational]) -> Option<usize> {
    let degree = poly_degree(poly)?;
    if degree == 0 || !poly[degree].is_one() {
        return None;
    }
    Some(degree)
}

/// A primitive element `θ = α + k·β` for `ℚ(α, β)`, with a certificate.
///
/// `f` and `g` must be monic and non-constant; they are the minimal
/// polynomials of `α` and `β`. The search runs `k = 1, 2, …` until
/// `Res_y(f(θ − k·y), g(y))` is squarefree of degree `deg f · deg g`, which
/// happens for all but finitely many `k`; `α` and `β` are then recovered from
/// `gcd(f(θ − k·y), g(y))` in `ℚ(θ)[y]`, which is linear in `y` exactly
/// because the resultant is squarefree.
///
/// # Errors
///
/// [`IdealDecline::GeneratorPolynomialNotMonic`] for a bad input, and
/// [`IdealDecline::NoPrimitiveElementFound`] when the search reached
/// [`PRIMITIVE_ELEMENT_SEARCH_BOUND`] — an honest "did not run to the end",
/// never a claim that no primitive element exists.
pub fn primitive_element(
    first: &[BigRational],
    second: &[BigRational],
) -> Result<PrimitiveElementCertificate, IdealDecline> {
    let first_degree = monic_degree(first).ok_or(IdealDecline::GeneratorPolynomialNotMonic)?;
    let second_degree = monic_degree(second).ok_or(IdealDecline::GeneratorPolynomialNotMonic)?;
    let expected = first_degree * second_degree;
    for step in 1..=PRIMITIVE_ELEMENT_SEARCH_BOUND {
        let multiplier = BigInt::from(step);
        let rational = BigRational::from_integer(multiplier.clone());
        let Some(theta_minpoly) = compositum_resultant(first, second, &rational) else {
            continue;
        };
        if poly_degree(&theta_minpoly) != Some(expected) || !poly_is_squarefree(&theta_minpoly) {
            continue;
        }
        let Some(certificate) = build_primitive_element(first, second, &multiplier, &theta_minpoly)
        else {
            continue;
        };
        if certificate.verify().is_ok() {
            return Ok(certificate);
        }
    }
    Err(IdealDecline::NoPrimitiveElementFound {
        bound: PRIMITIVE_ELEMENT_SEARCH_BOUND,
    })
}

/// Recover `β` from `gcd(f(θ − k·y), g(y))` in `ℚ(θ)[y]` and `α` from
/// `α = θ − k·β`.
fn build_primitive_element(
    first: &[BigRational],
    second: &[BigRational],
    multiplier: &BigInt,
    theta_minpoly: &[BigRational],
) -> Option<PrimitiveElementCertificate> {
    let field = NumberField::new(theta_minpoly).ok()?;
    let rational = BigRational::from_integer(multiplier.clone());
    let shifted = lift_shifted(&field, first, &rational)?;
    let lifted_second: Vec<Element> = second
        .iter()
        .map(|coefficient| field.rational(coefficient))
        .collect();
    let gcd = kpoly_gcd(&shifted, &kpoly_trim(lifted_second))?;
    if kpoly_degree(&gcd) != Some(1) {
        return None;
    }
    // gcd is monic, so it is y − β.
    let beta = gcd[0].neg();
    let alpha = field.generator().sub(&beta.scale(&rational))?;
    Some(PrimitiveElementCertificate {
        first_minpoly: poly_trim(first.to_vec()),
        second_minpoly: poly_trim(second.to_vec()),
        multiplier: multiplier.clone(),
        theta_minpoly: poly_trim(theta_minpoly.to_vec()),
        first_in_theta: alpha.coeffs().to_vec(),
        second_in_theta: beta.coeffs().to_vec(),
    })
}

// ---------------------------------------------------------------------------
// The class group as a group (wave three)
// ---------------------------------------------------------------------------

// Declared here with `#[path]` rather than in `lib.rs` so that the class-group
// law is reachable at `numberfield_ideals::` -- the same path as the class
// number it is a law on -- and so that `lib.rs`, which every lane touches, does
// not become one more shared append point. The child module is what lets the
// composition guards read this module's private `big_gcd`, `big_ext_gcd` and
// `big_mod_positive` without widening them to the crate.
// `pub` so rustdoc renders the module documentation and CHECKS its intra-doc
// links; a private module's `//!` block is generated nowhere and its links are
// never resolved, so `-D warnings` would pass over it silently.
#[path = "numberfield_classgroup.rs"]
pub mod numberfield_classgroup;

pub use numberfield_classgroup::{
    BezoutData, CLASS_GROUP_ORDER_BOUND, ClassGroupCertificate, ClassGroupCertificateError,
    ClassGroupDecline, CompositionCertificate, FormIdealCertificate, FormReductionCertificate,
    PrincipalityCertificate, REDUCTION_STEP_BOUND, ReductionStep, class_group, class_of_ideal,
    compose, form_of_ideal, ideal_of_form, is_principal, opposite_form, principal_form,
    reduce_form,
};

#[cfg(test)]
mod tests {
    use super::*;

    fn order(radicand: i64) -> QuadraticOrder {
        QuadraticOrder::new(&BigInt::from(radicand)).expect("order")
    }

    fn element(rational: i64, omega: i64) -> OrderElement {
        OrderElement::from_i64(rational, omega)
    }

    fn ideal(a: i64, b: i64, c: i64) -> Ideal {
        Ideal::from_i64(a, b, c)
    }

    fn poly(coefficients: &[i64]) -> Vec<BigRational> {
        coefficients
            .iter()
            .map(|&value| BigRational::from_integer(BigInt::from(value)))
            .collect()
    }

    fn ratio(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn factor_map(certificate: &IdealFactorizationCertificate) -> BTreeMap<Ideal, u32> {
        certificate.factors.iter().cloned().collect()
    }

    fn merge_into(target: &mut BTreeMap<Ideal, u32>, certificate: &IdealFactorizationCertificate) {
        for (prime, exponent) in &certificate.factors {
            *target.entry(prime.clone()).or_insert(0) += exponent;
        }
    }

    fn product_certificate(
        order: &QuadraticOrder,
        left: &Ideal,
        right: &Ideal,
    ) -> IdealProductCertificate {
        order.multiply_ideals(left, right).expect("product").1
    }

    // -----------------------------------------------------------------
    // The order itself
    // -----------------------------------------------------------------

    #[test]
    fn gaussian_order_has_omega_equal_to_i_and_discriminant_minus_four() {
        let order = order(-1);
        assert_eq!(order.omega_trace(), &BigInt::from(0));
        assert_eq!(order.omega_constant(), &BigInt::from(-1));
        assert_eq!(order.discriminant(), &BigInt::from(-4));
    }

    #[test]
    fn one_mod_four_order_has_half_integer_omega_and_odd_discriminant() {
        let order = order(5);
        assert_eq!(order.omega_trace(), &BigInt::from(1));
        assert_eq!(order.omega_constant(), &BigInt::from(1));
        assert_eq!(order.discriminant(), &BigInt::from(5));
        // ω² = ω + 1, the golden ratio relation.
        let omega = element(0, 1);
        assert_eq!(order.multiply(&omega, &omega), element(1, 1));
    }

    #[test]
    fn minus_five_order_is_the_two_three_case() {
        let order = order(-5);
        assert_eq!(order.omega_trace(), &BigInt::from(0));
        assert_eq!(order.omega_constant(), &BigInt::from(-5));
        assert_eq!(order.discriminant(), &BigInt::from(-20));
        assert_eq!(order.element_norm(&element(1, 1)), BigInt::from(6));
    }

    #[test]
    fn ideal_norm_and_containment_are_read_off_the_hermite_basis() {
        let order = order(-1);
        let prime = order.principal_ideal(&element(1, 1)).expect("ideal");
        assert_eq!(prime, ideal(2, 1, 1));
        assert_eq!(prime.norm(), BigInt::from(2));
        assert!(prime.contains_element(&element(1, 1)));
        assert!(prime.contains_element(&element(2, 0)));
        assert!(!prime.contains_element(&element(1, 0)));
        assert!(prime.contains(&order.rational_ideal(&BigInt::from(2)).expect("two")));
        assert!(order.unit_ideal().contains_element(&element(1, 1)));
    }

    // -----------------------------------------------------------------
    // Ideal multiplication
    // -----------------------------------------------------------------

    #[test]
    fn in_the_gaussian_integers_two_is_the_square_of_one_plus_i() {
        let order = order(-1);
        let prime = order.principal_ideal(&element(1, 1)).expect("ideal");
        let (square, certificate) = order.multiply_ideals(&prime, &prime).expect("square");
        certificate.verify().expect("square verifies");
        assert_eq!(square, order.rational_ideal(&BigInt::from(2)).expect("two"));
        assert_eq!(square.norm(), BigInt::from(4));
    }

    #[test]
    fn multiplying_by_the_unit_ideal_is_the_identity_and_certifies() {
        let order = order(-5);
        let prime = ideal(3, 1, 1);
        let (product, certificate) = order
            .multiply_ideals(&prime, &order.unit_ideal())
            .expect("product");
        certificate.verify().expect("verifies");
        assert_eq!(product, prime);
    }

    #[test]
    fn ideal_power_agrees_with_repeated_multiplication() {
        let order = order(-5);
        let prime = ideal(2, 1, 1);
        let cube = order.ideal_power(&prime, 3).expect("cube");
        let (square, _) = order.multiply_ideals(&prime, &prime).expect("square");
        let (expected, _) = order.multiply_ideals(&square, &prime).expect("cube");
        assert_eq!(cube, expected);
    }

    // -----------------------------------------------------------------
    // Splitting of rational primes
    // -----------------------------------------------------------------

    fn splitting(radicand: i64, prime: i64) -> (Vec<Ideal>, PrimeSplittingCertificate) {
        let order = order(radicand);
        let result = order.split_prime(&BigInt::from(prime)).expect("splits");
        result.1.verify().expect("splitting verifies");
        result
    }

    #[test]
    fn gaussian_five_splits_three_is_inert_and_two_ramifies() {
        let (factors, certificate) = splitting(-1, 5);
        assert_eq!(certificate.splitting, SplittingType::Split);
        assert_eq!(factors, vec![ideal(5, 2, 1), ideal(5, 3, 1)]);

        let (factors, certificate) = splitting(-1, 3);
        assert_eq!(certificate.splitting, SplittingType::Inert);
        assert_eq!(factors, vec![ideal(3, 0, 3)]);
        assert_eq!(factors[0].norm(), BigInt::from(9));

        let (factors, certificate) = splitting(-1, 2);
        assert_eq!(certificate.splitting, SplittingType::Ramified);
        assert_eq!(factors, vec![ideal(2, 1, 1), ideal(2, 1, 1)]);
    }

    #[test]
    fn minus_five_two_ramifies_three_splits_and_eleven_is_inert() {
        let (factors, certificate) = splitting(-5, 2);
        assert_eq!(certificate.splitting, SplittingType::Ramified);
        assert_eq!(factors, vec![ideal(2, 1, 1), ideal(2, 1, 1)]);

        let (factors, certificate) = splitting(-5, 3);
        assert_eq!(certificate.splitting, SplittingType::Split);
        assert_eq!(factors, vec![ideal(3, 1, 1), ideal(3, 2, 1)]);

        let (factors, certificate) = splitting(-5, 11);
        assert_eq!(certificate.splitting, SplittingType::Inert);
        assert_eq!(factors, vec![ideal(11, 0, 11)]);
    }

    #[test]
    fn in_the_omega_case_five_ramifies_eleven_splits_and_two_is_inert() {
        let (factors, certificate) = splitting(5, 5);
        assert_eq!(certificate.splitting, SplittingType::Ramified);
        assert_eq!(factors[0], factors[1]);
        assert_eq!(factors[0].norm(), BigInt::from(5));

        let (factors, certificate) = splitting(5, 11);
        assert_eq!(certificate.splitting, SplittingType::Split);
        assert_ne!(factors[0], factors[1]);
        assert_eq!(factors[0].norm(), BigInt::from(11));

        let (factors, certificate) = splitting(5, 2);
        assert_eq!(certificate.splitting, SplittingType::Inert);
        assert_eq!(factors[0].norm(), BigInt::from(4));
    }

    #[test]
    fn splitting_declines_on_a_composite_and_on_an_oversized_argument() {
        let order = order(-1);
        assert_eq!(
            order.split_prime(&BigInt::from(9)),
            Err(IdealDecline::NotPrime)
        );
        let huge = BigInt::from(1) << 200;
        assert_eq!(
            order.split_prime(&huge),
            Err(IdealDecline::MagnitudeOutOfRange)
        );
    }

    // -----------------------------------------------------------------
    // The standard non-unique-factorization example
    // -----------------------------------------------------------------

    #[test]
    fn the_prime_above_two_in_z_root_minus_five_is_not_principal() {
        let order = order(-5);
        let prime = ideal(2, 1, 1);
        assert_eq!(prime.norm(), BigInt::from(2));
        // N(u + v√−5) = u² + 5v² = 2 has no solution: v = 0 forces u² = 2 and
        // |v| ≥ 1 forces the norm ≥ 5. The bounded sweep is exhaustive for
        // that reason, not merely a sample.
        for u in -3i64..=3 {
            for v in -3i64..=3 {
                assert_ne!(order.element_norm(&element(u, v)).abs(), BigInt::from(2));
            }
        }
    }

    #[test]
    fn six_factors_as_p2_squared_times_the_two_primes_over_three() {
        let order = order(-5);
        let six = order.rational_ideal(&BigInt::from(6)).expect("six");
        let certificate = order.factor_ideal(&six).expect("factors");
        certificate.verify().expect("verifies");
        let expected: BTreeMap<Ideal, u32> = [
            (ideal(2, 1, 1), 2),
            (ideal(3, 1, 1), 1),
            (ideal(3, 2, 1), 1),
        ]
        .into_iter()
        .collect();
        assert_eq!(factor_map(&certificate), expected);
        assert_eq!(six.norm(), BigInt::from(36));
    }

    #[test]
    fn the_two_element_factorizations_of_six_give_the_same_ideal_factorization() {
        let order = order(-5);
        let six = order.rational_ideal(&BigInt::from(6)).expect("six");
        let reference = order.factor_ideal(&six).expect("factors");
        reference.verify().expect("verifies");

        // 6 = 2 · 3
        let mut rational_route: BTreeMap<Ideal, u32> = BTreeMap::new();
        for value in [2i64, 3] {
            let ideal = order.rational_ideal(&BigInt::from(value)).expect("ideal");
            let certificate = order.factor_ideal(&ideal).expect("factors");
            certificate.verify().expect("verifies");
            merge_into(&mut rational_route, &certificate);
        }

        // 6 = (1 + √−5)(1 − √−5)
        let mut irrational_route: BTreeMap<Ideal, u32> = BTreeMap::new();
        for omega in [1i64, -1] {
            let (_, certificate) = order
                .factor_principal_ideal(&element(1, omega))
                .expect("factors");
            certificate.verify().expect("verifies");
            merge_into(&mut irrational_route, &certificate);
        }

        assert_eq!(rational_route, factor_map(&reference));
        assert_eq!(irrational_route, factor_map(&reference));
        // The elements really are irreducible-but-not-prime: each has exactly
        // two prime ideals above it, neither of them principal.
        assert_eq!(irrational_route.values().sum::<u32>(), 4);
    }

    #[test]
    fn one_plus_root_minus_five_factors_into_two_prime_ideals() {
        let order = order(-5);
        let (principal, certificate) = order
            .factor_principal_ideal(&element(1, 1))
            .expect("factors");
        certificate.verify().expect("verifies");
        assert_eq!(principal.norm(), BigInt::from(6));
        assert_eq!(
            certificate.factors,
            vec![(ideal(2, 1, 1), 1), (ideal(3, 1, 1), 1)]
        );
    }

    #[test]
    fn factoring_declines_on_the_zero_element() {
        let order = order(-5);
        assert_eq!(
            order.factor_principal_ideal(&element(0, 0)),
            Err(IdealDecline::ZeroInput)
        );
    }

    // -----------------------------------------------------------------
    // Class numbers
    // -----------------------------------------------------------------

    fn class_number_of(discriminant: i64) -> usize {
        let (count, certificate) = class_number(&BigInt::from(discriminant)).expect("class number");
        certificate.verify().expect("class number verifies");
        assert_eq!(count, certificate.class_number());
        count
    }

    #[test]
    fn imaginary_quadratic_class_numbers_match_the_classical_values() {
        assert_eq!(class_number_of(-4), 1);
        assert_eq!(class_number_of(-20), 2);
        assert_eq!(class_number_of(-23), 3);
        assert_eq!(class_number_of(-163), 1);
        assert_eq!(class_number_of(-47), 5);
    }

    #[test]
    fn the_reduced_forms_of_discriminant_minus_twenty_are_the_expected_two() {
        let (_, certificate) = class_number(&BigInt::from(-20)).expect("class number");
        certificate.verify().expect("verifies");
        assert_eq!(
            certificate.forms,
            vec![
                BinaryQuadraticForm::from_i64(1, 0, 5),
                BinaryQuadraticForm::from_i64(2, 2, 3),
            ]
        );
    }

    #[test]
    fn the_class_number_of_an_order_is_the_class_number_of_its_discriminant() {
        let order = order(-5);
        let (count, certificate) = order.class_number().expect("class number");
        certificate.verify().expect("verifies");
        assert_eq!(count, 2);
        assert_eq!(certificate.discriminant, BigInt::from(-20));
    }

    #[test]
    fn class_number_declines_outside_its_hypothesis() {
        assert_eq!(
            class_number(&BigInt::from(5)),
            Err(IdealDecline::DiscriminantNotNegative)
        );
        assert_eq!(
            class_number(&BigInt::from(-6)),
            Err(IdealDecline::DiscriminantNotAdmissible)
        );
        assert_eq!(
            class_number(&BigInt::from(-100_000_004i64)),
            Err(IdealDecline::DiscriminantTooLarge {
                bound: CLASS_NUMBER_DISCRIMINANT_BOUND
            })
        );
        let order = order(5);
        assert_eq!(
            order.class_number(),
            Err(IdealDecline::DiscriminantNotNegative)
        );
    }

    // -----------------------------------------------------------------
    // Primitive elements
    // -----------------------------------------------------------------

    #[test]
    fn root_two_and_root_three_generate_a_quartic_with_recorded_expressions() {
        let certificate =
            primitive_element(&poly(&[-2, 0, 1]), &poly(&[-3, 0, 1])).expect("primitive element");
        certificate.verify().expect("verifies");
        assert_eq!(certificate.multiplier, BigInt::from(1));
        assert_eq!(certificate.theta_minpoly, poly(&[1, 0, -10, 0, 1]));
        assert_eq!(certificate.degree(), 4);
        // √2 = (θ³ − 9θ)/2 and √3 = (11θ − θ³)/2.
        assert_eq!(
            certificate.first_in_theta,
            vec![
                BigRational::zero(),
                ratio(-9, 2),
                BigRational::zero(),
                ratio(1, 2)
            ]
        );
        assert_eq!(
            certificate.second_in_theta,
            vec![
                BigRational::zero(),
                ratio(11, 2),
                BigRational::zero(),
                ratio(-1, 2)
            ]
        );
    }

    #[test]
    fn cube_root_of_two_and_root_two_generate_a_sextic() {
        let certificate = primitive_element(&poly(&[-2, 0, 0, 1]), &poly(&[-2, 0, 1]))
            .expect("primitive element");
        certificate.verify().expect("verifies");
        assert_eq!(certificate.degree(), 6);
        assert_eq!(poly_degree(&certificate.theta_minpoly), Some(6));
    }

    #[test]
    fn primitive_element_declines_on_a_non_monic_minimal_polynomial() {
        assert_eq!(
            primitive_element(&poly(&[-2, 0, 2]), &poly(&[-3, 0, 1])),
            Err(IdealDecline::GeneratorPolynomialNotMonic)
        );
        assert_eq!(
            primitive_element(&poly(&[-2, 0, 1]), &poly(&[1])),
            Err(IdealDecline::GeneratorPolynomialNotMonic)
        );
    }

    // -----------------------------------------------------------------
    // Guards: the Hermite normal form conditions
    // -----------------------------------------------------------------

    #[test]
    fn forged_ideal_with_a_non_positive_leading_coefficient_is_refused() {
        assert_eq!(
            ideal(0, 0, 1).admissible_in(&order(-1)),
            Err(IdealCertificateError::BasisLeadingNotPositive)
        );
    }

    #[test]
    fn forged_ideal_with_a_non_positive_denominator_is_refused() {
        assert_eq!(
            ideal(2, 0, 0).admissible_in(&order(-1)),
            Err(IdealCertificateError::BasisDenominatorNotPositive)
        );
    }

    #[test]
    fn forged_ideal_with_an_unreduced_off_diagonal_is_refused() {
        assert_eq!(
            ideal(2, 5, 1).admissible_in(&order(-1)),
            Err(IdealCertificateError::BasisOffDiagonalNotReduced)
        );
        assert_eq!(
            ideal(2, -1, 1).admissible_in(&order(-1)),
            Err(IdealCertificateError::BasisOffDiagonalNotReduced)
        );
    }

    #[test]
    fn forged_ideal_whose_denominator_misses_the_leading_coefficient_is_refused() {
        assert_eq!(
            ideal(3, 0, 2).admissible_in(&order(-1)),
            Err(IdealCertificateError::BasisDenominatorDoesNotDivideLeading)
        );
    }

    #[test]
    fn forged_ideal_whose_denominator_misses_the_off_diagonal_is_refused() {
        assert_eq!(
            ideal(4, 1, 2).admissible_in(&order(-1)),
            Err(IdealCertificateError::BasisDenominatorDoesNotDivideOffDiagonal)
        );
    }

    #[test]
    fn forged_module_that_is_not_closed_under_omega_is_refused() {
        // [3, ω] passes every divisibility condition but 3 ∤ N(ω) = 1.
        assert_eq!(
            ideal(3, 0, 1).admissible_in(&order(-1)),
            Err(IdealCertificateError::BasisNotClosedUnderOmega)
        );
    }

    // -----------------------------------------------------------------
    // Guards: the product certificate
    // -----------------------------------------------------------------

    #[test]
    fn product_certificate_with_wrong_order_parameters_is_refused() {
        let order = order(-1);
        let mut certificate = product_certificate(&order, &ideal(2, 1, 1), &ideal(2, 1, 1));
        certificate.omega_trace = BigInt::from(5);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::OrderParametersMismatch)
        );
    }

    #[test]
    fn product_certificate_with_a_forged_factor_is_refused() {
        let order = order(-1);
        let mut certificate = product_certificate(&order, &ideal(2, 1, 1), &ideal(2, 1, 1));
        certificate.left = ideal(0, 0, 1);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::BasisLeadingNotPositive)
        );
    }

    #[test]
    fn product_certificate_with_a_forged_right_factor_is_refused() {
        let order = order(-1);
        let mut certificate = product_certificate(&order, &ideal(2, 1, 1), &ideal(2, 1, 1));
        certificate.right = ideal(2, 0, 0);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::BasisDenominatorNotPositive)
        );
    }

    #[test]
    fn product_certificate_whose_claimed_product_is_not_an_ideal_is_refused() {
        let order = order(-1);
        let mut certificate = product_certificate(&order, &ideal(2, 1, 1), &ideal(2, 1, 1));
        certificate.product = ideal(4, 1, 2);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::BasisDenominatorDoesNotDivideOffDiagonal)
        );
    }

    #[test]
    fn product_certificate_with_an_extra_generator_product_is_refused() {
        let order = order(-1);
        let mut certificate = product_certificate(&order, &ideal(2, 1, 1), &ideal(2, 1, 1));
        certificate.generator_products.push(element(0, 0));
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::GeneratorProductMismatch { index: 4 })
        );
    }

    #[test]
    fn product_certificate_with_a_forged_generator_product_is_refused() {
        let order = order(-1);
        let mut certificate = product_certificate(&order, &ideal(2, 1, 1), &ideal(2, 1, 1));
        certificate.generator_products[0] = element(7, 7);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::GeneratorProductMismatch { index: 0 })
        );
    }

    #[test]
    fn product_certificate_missing_a_generator_product_is_refused() {
        let order = order(-1);
        let mut certificate = product_certificate(&order, &ideal(2, 1, 1), &ideal(2, 1, 1));
        certificate.generator_products.pop();
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::GeneratorProductMismatch { index: 3 })
        );
    }

    #[test]
    fn product_certificate_with_a_wrong_norm_is_refused() {
        let order = order(-1);
        let mut certificate = product_certificate(&order, &ideal(2, 1, 1), &ideal(2, 1, 1));
        certificate.product = order.unit_ideal();
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::ProductNormMismatch)
        );
    }

    #[test]
    fn product_certificate_with_the_right_norm_but_the_wrong_ideal_is_refused() {
        let order = order(-5);
        let mut certificate = product_certificate(&order, &ideal(3, 1, 1), &order.unit_ideal());
        // (3, 2 + ω) has the same norm as (3, 1 + ω) and is a genuine ideal.
        certificate.product = ideal(3, 2, 1);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::ProductHermiteMismatch)
        );
    }

    // -----------------------------------------------------------------
    // Guards: the splitting certificate
    // -----------------------------------------------------------------

    fn splitting_certificate(radicand: i64, prime: i64) -> PrimeSplittingCertificate {
        order(radicand)
            .split_prime(&BigInt::from(prime))
            .expect("splits")
            .1
    }

    #[test]
    fn splitting_certificate_about_a_composite_is_refused() {
        let mut certificate = splitting_certificate(-5, 3);
        certificate.prime = BigInt::from(9);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::SplittingBaseNotPrime)
        );
    }

    #[test]
    fn splitting_certificate_with_a_wrong_discriminant_is_refused() {
        let mut certificate = splitting_certificate(-5, 3);
        certificate.discriminant = BigInt::from(-24);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::OrderParametersMismatch)
        );
    }

    #[test]
    fn splitting_certificate_claiming_the_wrong_type_is_refused() {
        let mut certificate = splitting_certificate(-1, 5);
        certificate.splitting = SplittingType::Inert;
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::SplittingTypeMismatch { symbol: 1 })
        );
    }

    #[test]
    fn splitting_certificate_with_the_wrong_number_of_factors_is_refused() {
        let mut certificate = splitting_certificate(-1, 5);
        certificate.factors.pop();
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::SplittingFactorCountMismatch {
                found: 1,
                expected: 2
            })
        );
    }

    #[test]
    fn a_split_certificate_listing_one_prime_twice_is_refused() {
        let mut certificate = splitting_certificate(-1, 5);
        certificate.factors[1] = certificate.factors[0].clone();
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::SplittingFactorDistinctnessMismatch)
        );
    }

    #[test]
    fn a_ramified_certificate_listing_two_different_primes_is_refused() {
        let mut certificate = splitting_certificate(-5, 2);
        certificate.factors[1] = ideal(3, 1, 1);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::SplittingFactorDistinctnessMismatch)
        );
    }

    #[test]
    fn splitting_certificate_with_a_forged_factor_basis_is_refused() {
        let mut certificate = splitting_certificate(-5, 3);
        certificate.factors[0] = ideal(3, 0, 2);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::BasisDenominatorDoesNotDivideLeading)
        );
    }

    #[test]
    fn splitting_certificate_whose_factors_do_not_multiply_back_is_refused() {
        let mut certificate = splitting_certificate(-5, 3);
        certificate.factors[0] = order(-5).unit_ideal();
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::SplittingProductMismatch)
        );
    }

    #[test]
    fn splitting_certificate_with_a_factor_of_the_wrong_norm_is_refused() {
        // (3) · (1) = (3) multiplies back correctly, but (3) has norm 9, not 3.
        let order = order(-5);
        let mut certificate = splitting_certificate(-5, 3);
        certificate.factors = vec![
            order.rational_ideal(&BigInt::from(3)).expect("three"),
            order.unit_ideal(),
        ];
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::PrimeIdealNormMismatch { index: 0 })
        );
    }

    // -----------------------------------------------------------------
    // Guards: the factorization certificate
    // -----------------------------------------------------------------

    fn factorization_certificate(radicand: i64, value: i64) -> IdealFactorizationCertificate {
        let order = order(radicand);
        let ideal = order.rational_ideal(&BigInt::from(value)).expect("ideal");
        order.factor_ideal(&ideal).expect("factors")
    }

    #[test]
    fn factorization_certificate_about_a_forged_ideal_is_refused() {
        let mut certificate = factorization_certificate(-5, 6);
        certificate.ideal = ideal(0, 0, 1);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::BasisLeadingNotPositive)
        );
    }

    #[test]
    fn factorization_certificate_with_a_zero_exponent_is_refused() {
        let mut certificate = factorization_certificate(-5, 6);
        certificate.factors[0].1 = 0;
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::ZeroExponent { index: 0 })
        );
    }

    #[test]
    fn factorization_certificate_naming_a_composite_norm_factor_is_refused() {
        let order = order(-5);
        let mut certificate = factorization_certificate(-5, 6);
        // (1 + √−5) has norm 6, which is neither a prime nor a prime square.
        certificate.factors[0].0 = order.principal_ideal(&element(1, 1)).expect("ideal");
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FactorNormNotAPrimePower { index: 0 })
        );
    }

    #[test]
    fn factorization_certificate_naming_a_non_prime_ideal_is_refused() {
        let order = order(-5);
        let mut certificate = factorization_certificate(-5, 6);
        // (2) has norm 4 = 2², but the only prime above 2 is (2, 1 + ω).
        certificate.factors[0].0 = order.rational_ideal(&BigInt::from(2)).expect("two");
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FactorIsNotAPrimeIdeal { index: 0 })
        );
    }

    #[test]
    fn factorization_certificate_missing_a_factor_is_refused_by_the_norm() {
        let mut certificate = factorization_certificate(-5, 6);
        certificate
            .factors
            .retain(|(prime, _)| prime != &ideal(3, 2, 1));
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FactorizationNormMismatch)
        );
    }

    #[test]
    fn factorization_certificate_with_the_right_norm_but_the_wrong_primes_is_refused() {
        let mut certificate = factorization_certificate(-5, 6);
        // Replace 𝔭₃ by 𝔭₃′, keeping every norm: 4 · 3 · 3 = 36 still.
        certificate.factors = vec![(ideal(2, 1, 1), 2), (ideal(3, 1, 1), 2)];
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FactorizationProductMismatch)
        );
    }

    #[test]
    fn factorization_certificate_with_wrong_order_parameters_is_refused() {
        let mut certificate = factorization_certificate(-5, 6);
        certificate.omega_constant = BigInt::from(7);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::OrderParametersMismatch)
        );
    }

    // -----------------------------------------------------------------
    // Guards: the class-number certificate
    // -----------------------------------------------------------------

    fn class_certificate(discriminant: i64) -> ClassNumberCertificate {
        class_number(&BigInt::from(discriminant))
            .expect("class number")
            .1
    }

    #[test]
    fn class_number_certificate_with_a_non_negative_discriminant_is_refused() {
        let mut certificate = class_certificate(-20);
        certificate.discriminant = BigInt::from(20);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::DiscriminantNotNegative)
        );
    }

    #[test]
    fn class_number_certificate_with_an_inadmissible_discriminant_is_refused() {
        let mut certificate = class_certificate(-20);
        certificate.discriminant = BigInt::from(-22);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::DiscriminantNotAdmissible)
        );
    }

    #[test]
    fn class_number_certificate_listing_a_form_of_another_discriminant_is_refused() {
        let mut certificate = class_certificate(-20);
        certificate.forms[0] = BinaryQuadraticForm::from_i64(1, 0, 6);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FormDiscriminantMismatch { index: 0 })
        );
    }

    #[test]
    fn class_number_certificate_listing_an_indefinite_form_is_refused() {
        let mut certificate = class_certificate(-20);
        // disc(−1, 0, −5) = −4·(−1)(−5) = −20, but a < 0.
        certificate.forms[0] = BinaryQuadraticForm::from_i64(-1, 0, -5);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FormNotPositiveDefinite { index: 0 })
        );
    }

    #[test]
    fn class_number_certificate_listing_an_imprimitive_form_is_refused() {
        let mut certificate = class_certificate(-16);
        // (2, 0, 2) is reduced of discriminant −16, but gcd(2, 0, 2) = 2.
        certificate
            .forms
            .push(BinaryQuadraticForm::from_i64(2, 0, 2));
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FormNotPrimitive { index: 1 })
        );
    }

    #[test]
    fn class_number_certificate_listing_a_non_reduced_form_is_refused() {
        let mut certificate = class_certificate(-20);
        // (5, 0, 1) has discriminant −20 and is primitive, but 5 > 1.
        certificate.forms[1] = BinaryQuadraticForm::from_i64(5, 0, 1);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FormNotReduced { index: 1 })
        );
    }

    #[test]
    fn class_number_certificate_listing_a_form_twice_is_refused() {
        let mut certificate = class_certificate(-20);
        certificate.forms[1] = certificate.forms[0].clone();
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::FormsNotDistinct { index: 1 })
        );
    }

    #[test]
    fn class_number_certificate_missing_a_form_is_refused_by_the_recount() {
        let mut certificate = class_certificate(-23);
        certificate.forms.pop();
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::ClassNumberRecountMismatch {
                claimed: 2,
                recounted: 3
            })
        );
    }

    // -----------------------------------------------------------------
    // Guards: the primitive-element certificate
    // -----------------------------------------------------------------

    fn primitive_certificate() -> PrimitiveElementCertificate {
        primitive_element(&poly(&[-2, 0, 1]), &poly(&[-3, 0, 1])).expect("primitive element")
    }

    #[test]
    fn primitive_element_certificate_with_a_non_monic_generator_is_refused() {
        let mut certificate = primitive_certificate();
        certificate.first_minpoly = poly(&[-2, 0, 2]);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::GeneratorPolynomialNotMonic)
        );
    }

    #[test]
    fn primitive_element_certificate_with_a_zero_multiplier_is_refused() {
        let mut certificate = primitive_certificate();
        certificate.multiplier = BigInt::from(0);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::PrimitiveElementMultiplierZero)
        );
    }

    #[test]
    fn primitive_element_certificate_of_the_wrong_degree_is_refused() {
        let mut certificate = primitive_certificate();
        certificate.theta_minpoly = poly(&[-2, 0, 1]);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::CompositumDegreeMismatch {
                found: 2,
                expected: 4
            })
        );
    }

    #[test]
    fn primitive_element_certificate_with_a_repeated_root_is_refused() {
        let mut certificate = primitive_certificate();
        // (x² − 1)² is monic of degree 4 and not squarefree.
        certificate.theta_minpoly = poly(&[1, 0, -2, 0, 1]);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::CompositumNotSquarefree)
        );
    }

    #[test]
    fn primitive_element_certificate_with_a_reducible_modulus_is_refused() {
        let mut certificate = primitive_certificate();
        // (x² − 2)(x² − 3) is monic, quartic and squarefree, but reducible.
        certificate.theta_minpoly = poly(&[6, 0, -5, 0, 1]);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::CompositumNotIrreducible)
        );
    }

    #[test]
    fn primitive_element_certificate_whose_alpha_does_not_satisfy_f_is_refused() {
        let mut certificate = primitive_certificate();
        certificate.first_in_theta = poly(&[1, 0, 0, 0]);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::AlphaDoesNotSatisfyF)
        );
    }

    #[test]
    fn primitive_element_certificate_whose_beta_does_not_satisfy_g_is_refused() {
        let mut certificate = primitive_certificate();
        certificate.second_in_theta = poly(&[1, 0, 0, 0]);
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::BetaDoesNotSatisfyG)
        );
    }

    #[test]
    fn primitive_element_certificate_whose_parts_do_not_sum_to_theta_is_refused() {
        let mut certificate = primitive_certificate();
        // −√3 also satisfies x² − 3, but √2 − √3 is not θ.
        certificate.second_in_theta = certificate
            .second_in_theta
            .iter()
            .map(|coefficient| -coefficient.clone())
            .collect();
        assert_eq!(
            certificate.verify(),
            Err(IdealCertificateError::PrimitiveElementRelationFails)
        );
    }

    // -----------------------------------------------------------------
    // Cost, ADVISORY. Run with `--ignored --nocapture` under `--release`.
    // -----------------------------------------------------------------

    #[test]
    #[ignore = "cost measurement, not a correctness gate; run under --release"]
    fn class_number_enumeration_cost_profile() {
        for magnitude in [1_000i64, 10_000] {
            let discriminant = -magnitude;
            let start = std::time::Instant::now();
            let (count, certificate) =
                class_number(&BigInt::from(discriminant)).expect("class number");
            let produced = start.elapsed();
            let start = std::time::Instant::now();
            certificate.verify().expect("verifies");
            let verified = start.elapsed();
            println!(
                "|D| = {}: h = {count}, produce {:?}, verify {:?}",
                discriminant.abs(),
                produced,
                verified
            );
        }
    }
}
