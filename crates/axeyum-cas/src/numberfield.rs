//! Algebraic number fields, Gaussian integers, and real quadratic fields.
//!
//! Item 4 of the CAS *Next Ten*, first slice. Everything here is exact and
//! arbitrary-precision: coefficients are [`BigRational`] and integers are
//! [`BigInt`], so nothing in this module overflows the way the `i128` core
//! does. No `f64` appears anywhere.
//!
//! # What this module computes
//!
//! - [`NumberField`] — a simple extension `ℚ(α) = ℚ[x]/(f)` for a **monic**
//!   `f` that is **irreducible over ℚ**. Irreducibility is decided, not
//!   assumed: [`NumberField::new`] runs the crate's own
//!   [`factor_univariate_over_q`] and refuses a reducible modulus with
//!   [`CertificateError::ReducibleModulus`], distinct from every other
//!   refusal.
//! - [`Element`] — an element of that field as a dense, least-significant-first
//!   coefficient vector of length `deg f`, with `add`, `sub`, `mul`, `pow`,
//!   [`Element::inverse`], [`Element::norm_trace`], and
//!   [`Element::minimal_polynomial`].
//! - [`GaussianInt`] — the ring `ℤ[i]` with norm, Euclidean
//!   [`GaussianInt::divmod`], [`GaussianInt::gcd`], and
//!   [`GaussianInt::factor`] into Gaussian primes times a unit.
//! - [`two_squares`] — a representation `n = a² + b²` or a *refutation*
//!   naming a prime `p ≡ 3 (mod 4)` occurring to odd multiplicity, with the
//!   crate's [`FactorizationCertificate`] attached.
//! - [`QuadraticField`] — `ℚ(√d)` for squarefree `d`, with the norm form
//!   `a² − d b²`, a unit test on `ℤ[√d]`, and
//!   [`QuadraticField::fundamental_unit`] from the continued fraction of `√d`.
//!
//! # What this module reuses (and does not reinvent)
//!
//! - **Factorization over ℚ**: [`crate::factor_univariate_over_q`]
//!   (Berlekamp–Zassenhaus) decides every irreducibility question here. It is
//!   `i128`-coefficiented, so the modulus is converted and a modulus whose
//!   coefficients do not fit is refused with
//!   [`CertificateError::IrreducibilityUndecided`] rather than assumed
//!   irreducible.
//! - **Integer factorization and primality**: [`crate::ntheory::factorize`]
//!   (trial division then Pollard rho, Miller–Rabin) and
//!   [`crate::ntheory::is_prime`].
//! - **Pratt certificates**: [`crate::ntheory_certify::certify_factorization`]
//!   and [`crate::ntheory_certify::check_factorization_certificate`] carry and
//!   re-check the factorization inside a two-squares refutation.
//! - **Tonelli–Shanks**: [`crate::ntheory_advanced::sqrt_mod`] supplies the
//!   `s` with `s² ≡ −1 (mod p)` that splits a prime `p ≡ 1 (mod 4)`. The split
//!   itself is `gcd(p, s + i)` in `ℤ[i]`, which is why **Cornacchia's
//!   algorithm is deliberately not implemented**: the Gaussian gcd already
//!   present here does the same job and is the object the certificate talks
//!   about anyway.
//! - **Continued fractions of `√d`**:
//!   [`crate::ntheory_advanced::sqrt_continued_fraction`] supplies `(a₀,
//!   period)`. The convergent recurrence is re-run here in [`BigInt`] rather
//!   than through `convergents`, because `convergents` is `i128` and the
//!   `d = 61` unit `1766319049 + 226153980√61` has a norm check near `3.1e18`
//!   — past `i64` and uncomfortably close to a fixed-width edge.
//!
//! What is **not** reused: there is no public arbitrary-precision polynomial
//! arithmetic in the workspace (`axeyum-ir`'s `poly_big` is private and its
//! two public entry points take a private type alias), so the `BigRational`
//! `ℚ[x]` helpers at the top of this file are new. The public `axeyum_ir::poly`
//! API is `i128` and would overflow on the `x⁴ − 10x² + 1` char-poly work.
//!
//! # What is certified, and what is `uncertified`
//!
//! Every certificate's `verify` re-derives the claim from the data alone and
//! never consults how the producer found it.
//!
//! | producer | certificate | guards |
//! |---|---|---|
//! | [`Element::inverse`] | [`InverseCertificate`] | degree shape; `a · a⁻¹ ≡ 1 (mod f)` re-multiplied and reduced; a zero element has no inverse |
//! | [`Element::norm_trace`] | [`NormTraceCertificate`] | the multiplication matrix is rebuilt from `f` and the element; the characteristic polynomial is monic of degree `n`; Cayley–Hamilton `χ(M) = 0`; `norm = (−1)ⁿ χ(0)`; `trace = −χ_{n−1}`; and — independently of `χ` — `norm = det M` by fraction-free elimination and `trace = tr M` by summing the diagonal |
//! | [`Element::minimal_polynomial`] | [`ElementMinPolyCertificate`] | the claimed polynomial is monic; the element satisfies it in the field; it is irreducible over ℚ. Those three together *are* the definition — a monic irreducible annihilator is the minimal polynomial — so no redundant "minimality" guard is shipped that no forgery could reach |
//! | [`GaussianInt::factor`] | [`GaussianFactorizationCertificate`] | the value is nonzero; the unit is one of `{1, −1, i, −i}`; `unit · ∏ factors = value`; every factor is a Gaussian prime (prime norm, or an inert rational prime `≡ 3 (mod 4)` up to a unit) |
//! | [`two_squares`] | [`TwoSquaresCertificate`] | representation: `n ≥ 0` and `a² + b² = n` recomputed exactly. refutation: the attached [`FactorizationCertificate`] re-checked against `n`; the named prime occurs in it with the claimed exponent; the prime is `≡ 3 (mod 4)`; the exponent is odd |
//! | [`QuadraticField::fundamental_unit`] | [`FundamentalUnitCertificate`] | `d > 1` and not a perfect square; `a² − d b² = norm`; `norm = ±1`; `a, b > 0`; **and, only below the search bound**, an independent exhaustive re-search over `1 ≤ y < b` |
//!
//! **`uncertified`, and why.**
//!
//! - The ring operations `add`, `sub`, `neg`, `mul`, `pow`, `scale` on
//!   [`Element`] and [`GaussianInt`], and [`Element::multiplication_matrix`].
//!   Checking a product costs a product; a certificate for them would be the
//!   producer wearing a hat. Same reasoning as [`crate::fps`].
//! - [`Element::norm`] and [`Element::trace`] are the convenience views of
//!   [`Element::norm_trace`]; the certificate is the certified route.
//! - **The "fundamental" half of [`QuadraticField::fundamental_unit`] beyond
//!   [`MINIMALITY_SEARCH_BOUND`]** (`10_000`). Below it the certificate
//!   carries [`Minimality::ExhaustiveBelow`] and `verify` re-runs the whole
//!   search, so *fundamental* is proved. Above it — `d = 61`, whose unit has
//!   `b = 226_153_980` — the certificate carries
//!   [`Minimality::Uncertified`] and `verify` checks only that the value **is
//!   a unit**. That it is the *smallest* unit rests on the classical theorem
//!   that every unit of `ℤ[√d]` with `a, b > 0` appears among the convergents
//!   of `√d`, which this module does not check. The claim is labelled, never
//!   promoted. Use [`FundamentalUnitCertificate::is_fully_certified`] to tell
//!   the two apart.
//! - **Two-squares refutations above [`PRATT_CERTIFY_BOUND`]** decline rather
//!   than ship an unchecked factorization: see
//!   [`DeclineReason::PrattCertificationTooExpensive`]. `2⁸⁹ − 1` is such a
//!   case — it is prime, `≡ 3 (mod 4)`, and therefore genuinely not a sum of
//!   two squares, but the Pratt certificate for it requires the full recursive
//!   factorization of `2⁸⁹ − 2`. The module declines with a named reason
//!   instead of asserting the refutation on the producer's word.
//!
//! # Out of scope, deliberately
//!
//! - **Ideal factorization, class groups, class numbers, ring of integers.**
//!   This slice is *element* arithmetic. `ℤ[√d]` is used as the unit ring even
//!   when `d ≡ 1 (mod 4)` makes the maximal order `ℤ[(1+√d)/2]` strictly
//!   larger, and the doc on [`QuadraticField::fundamental_unit`] says so.
//! - **Galois groups, relative extensions, compositum construction.** A
//!   multi-generator field such as `ℚ(√2, √3)` is handled only by presenting
//!   it as `ℚ(θ)` for a primitive element the caller supplies; no primitive
//!   element is searched for.
//! - **Multivariate factorization.** Named out of this slice up front.
//! - **Complex embeddings, real root selection, ordering.** An [`Element`] is
//!   an algebraic expression modulo `f`, not a located real number;
//!   [`crate::algebraic`] and [`crate::real_algebraic`] own that.
//!
//! # Cost profile
//!
//! **Not measured under `--release`, and not measured per operation.** What
//! *was* measured, 2026-09-05: the whole 65-test module sweep
//! (`cargo test -p axeyum-cas --lib numberfield::`) runs in **0.01 s to 0.20 s**
//! of wall clock in a **debug** build. That single number covers every case
//! this module ships — degree 2, 3 and 4 field arithmetic including inverses,
//! characteristic polynomials and element minimal polynomials; eight Gaussian
//! factorizations; the `2⁸⁹ − 1` decline; and the `d = 61` fundamental unit
//! **including its exhaustive minimality search over 3,804 candidates**. So no
//! individual operation here is expensive at these sizes, and the per-operation
//! split was not worth measuring. Treat the range as ADVISORY: it was taken on
//! a shared host under other lanes' load.
//!
//! What the shape says, independently of the clock: the field work is `O(n³)`
//! bignum linear algebra at `n ≤ 4`; the `d = 61` convergent walk is 23 steps
//! of a `BigInt` recurrence. The two things that can actually cost is (a) the
//! `i128` integer factorizer, which dominates [`two_squares`] and
//! [`GaussianInt::factor`] and is why both carry magnitude guards, and (b) the
//! minimality search, which is `b` iterations and is why it is bounded by
//! [`MINIMALITY_SEARCH_BOUND`] and labelled rather than run.

use core::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use axeyum_ir::Rational;

use crate::factor_univariate_over_q;
use crate::ntheory::{factorize, is_prime};
use crate::ntheory_advanced::{sqrt_continued_fraction, sqrt_mod};
use crate::ntheory_certify::{
    FactorizationCertificate, certify_factorization, check_factorization_certificate,
};

/// Largest `|n|` for which [`two_squares`] will attempt the Pratt certificates
/// a refutation needs.
///
/// Above this the module declines with
/// [`DeclineReason::PrattCertificationTooExpensive`] rather than assert a
/// refutation on the producer's word. The bound is a cost choice, not a
/// correctness one: `certify_factorization` is recursive over the factors of
/// `n − 1` for every prime `n`, and one adversarial input at the top of the
/// `i128` range would hang the gate.
pub const PRATT_CERTIFY_BOUND: i128 = 1_000_000_000_000_000_000;

/// Largest `b` for which [`FundamentalUnitCertificate`] proves minimality by
/// exhaustive search over `1 ≤ y < b`.
///
/// Above it the *fundamental* claim is labelled
/// [`Minimality::Uncertified`]; the unit claim itself is still checked.
pub const MINIMALITY_SEARCH_BOUND: u64 = 10_000;

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------

/// Why a certificate was refused, or why a field could not be built.
///
/// Each variant names a distinct, independently reachable guard, so a refusal
/// says *what* failed rather than merely that something did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertificateError {
    /// The modulus is the zero polynomial, a constant, or has a zero leading
    /// coefficient after trimming.
    ModulusDegenerate,
    /// The modulus is not monic. `ℚ[x]/(f)` is unchanged by scaling `f`, but
    /// this module requires the caller to have normalized so that a
    /// certificate's `minpoly` field is canonical.
    ModulusNotMonic,
    /// The modulus factors over ℚ, so `ℚ[x]/(f)` is not a field. Carries how
    /// many irreducible factors (with multiplicity) were found.
    ReducibleModulus {
        /// Number of non-constant irreducible factors counted with
        /// multiplicity; always at least two when this variant is raised.
        factors: u32,
    },
    /// Irreducibility could not be decided: a coefficient did not fit the
    /// `i128` factorizer, or the factorizer itself declined (degree cap,
    /// recombination cap). Never silently treated as irreducible.
    IrreducibilityUndecided,
    /// An element's coefficient vector has the wrong length for its field.
    DegreeMismatch {
        /// The field degree, which is the required length.
        expected: usize,
        /// The length actually carried.
        found: usize,
    },
    /// A certificate mixes elements that do not live in the same field.
    FieldMismatch,
    /// The zero element was presented as invertible.
    ZeroIsNotInvertible,
    /// `a · a⁻¹ mod f` is not `1`; the first coefficient index at which the
    /// reduced product differs from `1`.
    NotAnInverse {
        /// Index of the first disagreeing coefficient.
        degree: usize,
    },
    /// The recorded multiplication matrix is not the one the element and the
    /// modulus determine.
    MultiplicationMatrixMismatch {
        /// Row of the first disagreeing entry.
        row: usize,
        /// Column of the first disagreeing entry.
        col: usize,
    },
    /// The recorded characteristic polynomial is not monic of degree `n`.
    CharPolyNotMonic,
    /// Cayley–Hamilton fails: `χ(M) ≠ 0`, so `χ` is not the characteristic
    /// polynomial of the recorded matrix.
    CayleyHamiltonFailed,
    /// The recorded norm is not `(−1)ⁿ χ(0)`.
    NormNotCharPolyConstant,
    /// The recorded trace is not `−χ_{n−1}`.
    TraceNotCharPolySubleading,
    /// The recorded norm is not `det M`, computed independently of `χ`.
    NormNotDeterminant,
    /// The recorded trace is not the sum of the diagonal of `M`.
    TraceNotMatrixTrace,
    /// A claimed minimal polynomial is not monic (or is constant).
    MinimalPolynomialNotMonic,
    /// The element does not satisfy its claimed minimal polynomial.
    MinimalPolynomialNotSatisfied,
    /// A claimed minimal polynomial is reducible over ℚ, so it is a proper
    /// multiple of the real one.
    MinimalPolynomialReducible,
    /// A Gaussian factorization was presented for `0`, which has none.
    ZeroHasNoFactorization,
    /// The recorded unit is not one of `1`, `−1`, `i`, `−i`.
    NotAGaussianUnit,
    /// `unit · ∏ factors` does not equal the value.
    GaussianProductMismatch,
    /// The factor at this index is not a Gaussian prime.
    NotAGaussianPrime {
        /// Index into the certificate's factor list.
        index: usize,
    },
    /// A magnitude in the certificate is past the range of the `i128`
    /// primality/factorization routines the checker reuses, so the claim
    /// cannot be re-derived.
    MagnitudeOutOfRange,
    /// A two-squares representation was presented for a negative `n`.
    NegativeSumOfSquares,
    /// `a² + b²` recomputed exactly does not equal `n`.
    SumOfSquaresMismatch,
    /// The attached factorization certificate does not check against `n`.
    FactorizationCertificateInvalid,
    /// The refutation names a prime/exponent pair the attached factorization
    /// does not contain.
    RefutationExponentNotInFactorization,
    /// The refutation names a prime that is not `≡ 3 (mod 4)`, so it proves
    /// nothing.
    RefutationPrimeNotThreeModFour,
    /// The refutation names an even exponent, which is no obstruction at all.
    RefutationExponentEven,
    /// The radicand of a quadratic field is `0`, `1`, or not squarefree.
    RadicandNotAdmissible,
    /// A fundamental-unit certificate whose `d` is `≤ 1` or a perfect square,
    /// where there is no fundamental unit to speak of.
    UnitRadicandNotRealQuadratic,
    /// `a² − d b²` recomputed does not equal the recorded norm.
    UnitNormMismatch,
    /// The recorded norm is not `±1`.
    NotAUnitNorm,
    /// The recorded unit does not have `a > 0` and `b > 0`, so "smallest" is
    /// not well posed against the recorded search.
    UnitNotPositive,
    /// A certificate claims an exhaustive search that does not reach `b − 1`.
    MinimalitySearchIncomplete {
        /// The count the certificate claims to have searched.
        claimed: u64,
        /// The count `b − 1` an exhaustive search must reach.
        required: u64,
    },
    /// The independent re-search found a strictly smaller unit.
    SmallerUnitExists {
        /// The `y` at which a smaller unit was found.
        witness: u64,
    },
}

impl fmt::Display for CertificateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// Why a producer declined to answer, as distinct from refusing a forged
/// certificate.
///
/// A decline is an honest "did not run", never a claim about the input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclineReason {
    /// The input was `0`, for which the operation is not defined.
    ZeroInput,
    /// A negative input where a non-negative one is required.
    NegativeInput,
    /// The magnitude exceeds the `i128` range of the crate's integer
    /// factorizer, which is the only factorizer in the workspace.
    MagnitudeOutOfRange,
    /// The crate's integer factorizer itself declined.
    FactorizationDeclined,
    /// The Pratt certificates a refutation must carry were not attempted:
    /// `|n|` is above [`PRATT_CERTIFY_BOUND`].
    PrattCertificationTooExpensive {
        /// The bound that was exceeded.
        bound: i128,
    },
    /// Tonelli–Shanks declined for this prime, so the split of a `p ≡ 1
    /// (mod 4)` could not be computed.
    SqrtModDeclined {
        /// The prime for which no square root of `−1` was produced.
        prime: i128,
    },
    /// After dividing out every prime the norm's factorization named, what
    /// remained was not a unit. Reachable only if a reused routine is wrong;
    /// declining is still better than shipping the residue as a "prime".
    FactorizationIncomplete,
    /// The radicand is not a positive non-square, so `ℤ[√d]` has no
    /// fundamental unit in the sense computed here.
    NotRealQuadratic,
    /// The continued fraction of `√d` did not produce a unit within the
    /// examined convergents.
    NoUnitFound,
}

impl fmt::Display for DeclineReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

// ---------------------------------------------------------------------------
// ℚ[x] over BigRational, least-significant-first
// ---------------------------------------------------------------------------

fn rat_zero() -> BigRational {
    BigRational::zero()
}

fn rat_one() -> BigRational {
    BigRational::one()
}

fn rat_int(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

/// Drop trailing zero coefficients so the leading entry is nonzero.
fn poly_trim(mut poly: Vec<BigRational>) -> Vec<BigRational> {
    while poly.last().is_some_and(num_traits::Zero::is_zero) {
        poly.pop();
    }
    poly
}

/// Degree, or `None` for the zero polynomial.
fn poly_degree(poly: &[BigRational]) -> Option<usize> {
    let mut index = poly.len();
    while index > 0 {
        index -= 1;
        if !poly[index].is_zero() {
            return Some(index);
        }
    }
    None
}

fn poly_add(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    let mut out = vec![rat_zero(); left.len().max(right.len())];
    for (index, value) in left.iter().enumerate() {
        out[index] += value;
    }
    for (index, value) in right.iter().enumerate() {
        out[index] += value;
    }
    poly_trim(out)
}

fn poly_sub(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    let mut out = vec![rat_zero(); left.len().max(right.len())];
    for (index, value) in left.iter().enumerate() {
        out[index] += value;
    }
    for (index, value) in right.iter().enumerate() {
        out[index] -= value;
    }
    poly_trim(out)
}

fn poly_mul(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut out = vec![rat_zero(); left.len() + right.len() - 1];
    for (i, a) in left.iter().enumerate() {
        if a.is_zero() {
            continue;
        }
        for (j, b) in right.iter().enumerate() {
            let term = a * b;
            out[i + j] += term;
        }
    }
    poly_trim(out)
}

fn poly_scale(poly: &[BigRational], factor: &BigRational) -> Vec<BigRational> {
    poly_trim(poly.iter().map(|c| c * factor).collect())
}

/// Long division in `ℚ[x]`. `None` exactly when `divisor` is the zero
/// polynomial.
fn poly_divrem(
    dividend: &[BigRational],
    divisor: &[BigRational],
) -> Option<(Vec<BigRational>, Vec<BigRational>)> {
    let divisor_degree = poly_degree(divisor)?;
    let lead_inverse = divisor[divisor_degree].clone().recip();
    let mut remainder = dividend.to_vec();
    let mut quotient = vec![rat_zero(); dividend.len().saturating_sub(divisor_degree) + 1];
    while let Some(remainder_degree) = poly_degree(&remainder) {
        if remainder_degree < divisor_degree {
            break;
        }
        let factor = &remainder[remainder_degree] * &lead_inverse;
        let shift = remainder_degree - divisor_degree;
        quotient[shift] = factor.clone();
        for index in 0..=divisor_degree {
            let term = &factor * &divisor[index];
            remainder[shift + index] -= term;
        }
        remainder = poly_trim(remainder);
    }
    Some((poly_trim(quotient), poly_trim(remainder)))
}

/// Extended Euclid in `ℚ[x]`: returns `(g, s, t)` with `s·a + t·b = g` and `g`
/// monic (or the zero polynomial when both inputs are zero).
fn poly_ext_gcd(
    left: &[BigRational],
    right: &[BigRational],
) -> (Vec<BigRational>, Vec<BigRational>, Vec<BigRational>) {
    let mut remainder_prev = poly_trim(left.to_vec());
    let mut remainder_curr = poly_trim(right.to_vec());
    let mut s_prev = vec![rat_one()];
    let mut s_curr: Vec<BigRational> = Vec::new();
    let mut t_prev: Vec<BigRational> = Vec::new();
    let mut t_curr = vec![rat_one()];
    while poly_degree(&remainder_curr).is_some() {
        // `remainder_curr` is nonzero here, so `poly_divrem` cannot fail.
        let Some((quotient, remainder)) = poly_divrem(&remainder_prev, &remainder_curr) else {
            break;
        };
        let s_next = poly_sub(&s_prev, &poly_mul(&quotient, &s_curr));
        let t_next = poly_sub(&t_prev, &poly_mul(&quotient, &t_curr));
        remainder_prev = core::mem::replace(&mut remainder_curr, remainder);
        s_prev = core::mem::replace(&mut s_curr, s_next);
        t_prev = core::mem::replace(&mut t_curr, t_next);
    }
    match poly_degree(&remainder_prev) {
        None => (remainder_prev, s_prev, t_prev),
        Some(degree) => {
            let inverse = remainder_prev[degree].clone().recip();
            (
                poly_scale(&remainder_prev, &inverse),
                poly_scale(&s_prev, &inverse),
                poly_scale(&t_prev, &inverse),
            )
        }
    }
}

/// Convert a `BigRational` coefficient vector to the `i128` `Rational` vector
/// the crate's factorizer takes. `None` if any numerator or denominator
/// overflows.
fn to_ir_poly(poly: &[BigRational]) -> Option<Vec<Rational>> {
    poly.iter()
        .map(|value| {
            let numerator = i128::try_from(value.numer()).ok()?;
            let denominator = i128::try_from(value.denom()).ok()?;
            Some(Rational::new(numerator, denominator))
        })
        .collect()
}

/// Whether `poly` is irreducible over ℚ, or `None` when the reused factorizer
/// could not decide (coefficients out of `i128` range, or its own caps).
fn is_irreducible_over_q(poly: &[BigRational]) -> Option<bool> {
    let converted = to_ir_poly(poly)?;
    let factors = factor_univariate_over_q(&converted)?;
    let total: u32 = factors.iter().map(|&(_, multiplicity)| multiplicity).sum();
    Some(total == 1)
}

/// Count of non-constant irreducible factors with multiplicity, for the
/// refusal message.
fn irreducible_factor_count(poly: &[BigRational]) -> Option<u32> {
    let converted = to_ir_poly(poly)?;
    let factors = factor_univariate_over_q(&converted)?;
    Some(factors.iter().map(|&(_, multiplicity)| multiplicity).sum())
}

// ---------------------------------------------------------------------------
// Rational linear algebra used by the norm/trace certificate
// ---------------------------------------------------------------------------

/// Determinant of a square `BigRational` matrix by Gaussian elimination with
/// exact pivoting. Independent of the Faddeev–LeVerrier route the producer
/// uses for the characteristic polynomial, which is the point.
fn matrix_determinant(matrix: &[Vec<BigRational>]) -> BigRational {
    let size = matrix.len();
    let mut work: Vec<Vec<BigRational>> = matrix.to_vec();
    let mut determinant = rat_one();
    for column in 0..size {
        let Some(pivot) = (column..size).find(|&row| !work[row][column].is_zero()) else {
            return rat_zero();
        };
        if pivot != column {
            work.swap(pivot, column);
            determinant = -determinant;
        }
        determinant *= &work[column][column];
        let inverse = work[column][column].clone().recip();
        let pivot_values = work[column].clone();
        for line in work.iter_mut().skip(column + 1) {
            if line[column].is_zero() {
                continue;
            }
            let factor = &line[column] * &inverse;
            for (index, pivot_value) in pivot_values.iter().enumerate().skip(column) {
                let term = &factor * pivot_value;
                line[index] -= term;
            }
        }
    }
    determinant
}

fn matrix_trace(matrix: &[Vec<BigRational>]) -> BigRational {
    let mut total = rat_zero();
    for (index, row) in matrix.iter().enumerate() {
        total += &row[index];
    }
    total
}

fn matrix_mul(left: &[Vec<BigRational>], right: &[Vec<BigRational>]) -> Vec<Vec<BigRational>> {
    let size = left.len();
    let mut out = vec![vec![rat_zero(); size]; size];
    for i in 0..size {
        for k in 0..size {
            if left[i][k].is_zero() {
                continue;
            }
            for j in 0..size {
                let term = &left[i][k] * &right[k][j];
                out[i][j] += term;
            }
        }
    }
    out
}

fn matrix_identity(size: usize) -> Vec<Vec<BigRational>> {
    let mut out = vec![vec![rat_zero(); size]; size];
    for (index, row) in out.iter_mut().enumerate() {
        row[index] = rat_one();
    }
    out
}

/// Characteristic polynomial of a square `BigRational` matrix by
/// Faddeev–LeVerrier, least-significant-first, monic of degree `size`.
fn char_poly_faddeev(matrix: &[Vec<BigRational>]) -> Vec<BigRational> {
    let size = matrix.len();
    let mut coefficients = vec![rat_zero(); size + 1];
    coefficients[size] = rat_one();
    let mut accumulator = vec![vec![rat_zero(); size]; size];
    for step in 1..=size {
        // accumulator <- A * accumulator + c[size - step + 1] * I
        let mut next = matrix_mul(matrix, &accumulator);
        let shift = coefficients[size - step + 1].clone();
        for (index, row) in next.iter_mut().enumerate() {
            row[index] += &shift;
        }
        accumulator = next;
        let product = matrix_mul(matrix, &accumulator);
        let trace = matrix_trace(&product);
        let divisor = BigRational::from_integer(BigInt::from(step));
        coefficients[size - step] = -(trace / divisor);
    }
    coefficients
}

/// Evaluate a `ℚ`-polynomial at a square matrix; the result is `0` exactly
/// when Cayley–Hamilton holds for `poly`.
fn matrix_poly_is_zero(poly: &[BigRational], matrix: &[Vec<BigRational>]) -> bool {
    let size = matrix.len();
    let mut accumulator = vec![vec![rat_zero(); size]; size];
    let mut power = matrix_identity(size);
    for coefficient in poly {
        if !coefficient.is_zero() {
            for (row_index, row) in power.iter().enumerate() {
                for (col_index, entry) in row.iter().enumerate() {
                    let term = coefficient * entry;
                    accumulator[row_index][col_index] += term;
                }
            }
        }
        power = matrix_mul(&power, matrix);
    }
    accumulator
        .iter()
        .all(|row| row.iter().all(num_traits::Zero::is_zero))
}

// ---------------------------------------------------------------------------
// NumberField
// ---------------------------------------------------------------------------

/// A simple algebraic extension `ℚ(α) = ℚ[x]/(f)`.
///
/// `f` is monic and irreducible over ℚ; both are checked at construction, so a
/// `NumberField` value is evidence that `ℚ[x]/(f)` really is a field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumberField {
    minpoly: Vec<BigRational>,
}

impl NumberField {
    /// Build `ℚ[x]/(f)` from a monic, least-significant-first `f`.
    ///
    /// # Errors
    ///
    /// - [`CertificateError::ModulusDegenerate`] if `f` is zero or constant.
    /// - [`CertificateError::ModulusNotMonic`] if the leading coefficient is
    ///   not `1`.
    /// - [`CertificateError::ReducibleModulus`] if `f` factors over ℚ. This is
    ///   how `x² − 1` is refused.
    /// - [`CertificateError::IrreducibilityUndecided`] if the reused
    ///   factorizer could not decide. Never treated as irreducible.
    pub fn new(minpoly: &[BigRational]) -> Result<NumberField, CertificateError> {
        let trimmed = poly_trim(minpoly.to_vec());
        let degree = poly_degree(&trimmed).ok_or(CertificateError::ModulusDegenerate)?;
        if degree == 0 {
            return Err(CertificateError::ModulusDegenerate);
        }
        if !trimmed[degree].is_one() {
            return Err(CertificateError::ModulusNotMonic);
        }
        match is_irreducible_over_q(&trimmed) {
            None => Err(CertificateError::IrreducibilityUndecided),
            Some(false) => Err(CertificateError::ReducibleModulus {
                factors: irreducible_factor_count(&trimmed).unwrap_or(0),
            }),
            Some(true) => Ok(NumberField { minpoly: trimmed }),
        }
    }

    /// The degree `[ℚ(α) : ℚ]`.
    #[must_use]
    pub fn degree(&self) -> usize {
        poly_degree(&self.minpoly).unwrap_or(0)
    }

    /// The monic minimal polynomial of the generator, least-significant-first.
    #[must_use]
    pub fn minimal_polynomial(&self) -> &[BigRational] {
        &self.minpoly
    }

    /// The element with the given coefficients, reduced modulo `f`.
    ///
    /// Coefficients are least-significant-first and may be longer or shorter
    /// than the degree; the result is always exactly `degree` long.
    #[must_use]
    pub fn element(&self, coeffs: &[BigRational]) -> Element {
        let reduced = self.reduce(coeffs);
        Element {
            field: self.clone(),
            coeffs: reduced,
        }
    }

    /// The zero element.
    #[must_use]
    pub fn zero(&self) -> Element {
        self.element(&[])
    }

    /// The multiplicative identity.
    #[must_use]
    pub fn one(&self) -> Element {
        self.element(&[rat_one()])
    }

    /// The generator `α`.
    #[must_use]
    pub fn generator(&self) -> Element {
        self.element(&[rat_zero(), rat_one()])
    }

    /// The image of a rational number in the field.
    #[must_use]
    pub fn rational(&self, value: &BigRational) -> Element {
        self.element(core::slice::from_ref(value))
    }

    fn reduce(&self, coeffs: &[BigRational]) -> Vec<BigRational> {
        let degree = self.degree();
        let remainder = poly_divrem(coeffs, &self.minpoly).map_or_else(Vec::new, |(_, r)| r);
        let mut out = vec![rat_zero(); degree];
        for (index, value) in remainder.into_iter().enumerate() {
            if index < degree {
                out[index] = value;
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Element
// ---------------------------------------------------------------------------

/// An element of a [`NumberField`], as a dense least-significant-first
/// coefficient vector of length `degree` in the power basis `1, α, …, α^{n−1}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Element {
    field: NumberField,
    coeffs: Vec<BigRational>,
}

impl Element {
    /// The field this element lives in.
    #[must_use]
    pub fn field(&self) -> &NumberField {
        &self.field
    }

    /// The coefficients in the power basis, least-significant-first, always
    /// exactly `field().degree()` long.
    #[must_use]
    pub fn coeffs(&self) -> &[BigRational] {
        &self.coeffs
    }

    /// Whether this is the zero element.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.coeffs.iter().all(num_traits::Zero::is_zero)
    }

    /// Sum. `None` if the two elements live in different fields.
    ///
    /// `uncertified`: checking a sum costs a sum.
    #[must_use]
    pub fn add(&self, other: &Element) -> Option<Element> {
        (self.field == other.field)
            .then(|| self.field.element(&poly_add(&self.coeffs, &other.coeffs)))
    }

    /// Difference. `None` if the two elements live in different fields.
    ///
    /// `uncertified`, for the same reason as [`Element::add`].
    #[must_use]
    pub fn sub(&self, other: &Element) -> Option<Element> {
        (self.field == other.field)
            .then(|| self.field.element(&poly_sub(&self.coeffs, &other.coeffs)))
    }

    /// Negation. `uncertified`.
    #[must_use]
    pub fn neg(&self) -> Element {
        self.field.element(&poly_sub(&[], &self.coeffs))
    }

    /// Product, reduced modulo the minimal polynomial. `None` if the two
    /// elements live in different fields.
    ///
    /// `uncertified`: checking a product costs a product.
    #[must_use]
    pub fn mul(&self, other: &Element) -> Option<Element> {
        (self.field == other.field)
            .then(|| self.field.element(&poly_mul(&self.coeffs, &other.coeffs)))
    }

    /// Scale by a rational. `uncertified`.
    #[must_use]
    pub fn scale(&self, factor: &BigRational) -> Element {
        self.field.element(&poly_scale(&self.coeffs, factor))
    }

    /// Repeated squaring power. `uncertified`.
    #[must_use]
    pub fn pow(&self, exponent: u32) -> Element {
        let mut result = self.field.one();
        let mut base = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining & 1 == 1 {
                result = result.mul(&base).unwrap_or_else(|| self.field.zero());
            }
            base = base.mul(&base).unwrap_or_else(|| self.field.zero());
            remaining >>= 1;
        }
        result
    }

    /// The matrix of multiplication-by-`self` in the power basis, row-major:
    /// entry `(i, j)` is the coefficient of `α^i` in `self · α^j`.
    ///
    /// `uncertified`; it is the raw object the certified
    /// [`Element::norm_trace`] talks about.
    #[must_use]
    pub fn multiplication_matrix(&self) -> Vec<Vec<BigRational>> {
        let degree = self.field.degree();
        // Column `j` is `self * alpha^j` reduced, so the matrix is the
        // transpose of this list.
        let columns: Vec<Vec<BigRational>> = (0..degree)
            .map(|column| {
                let mut shifted = vec![rat_zero(); column];
                shifted.push(rat_one());
                self.field.reduce(&poly_mul(&self.coeffs, &shifted))
            })
            .collect();
        let mut matrix = vec![vec![rat_zero(); degree]; degree];
        for (row, line) in matrix.iter_mut().enumerate() {
            for (col, entry) in line.iter_mut().enumerate() {
                entry.clone_from(&columns[col][row]);
            }
        }
        matrix
    }

    /// The multiplicative inverse together with a certificate, or `None` for
    /// the zero element.
    ///
    /// The inverse is computed by extended Euclid in `ℚ[x]`; the certificate's
    /// [`verify`](InverseCertificate::verify) re-multiplies and reduces
    /// instead, so it never consults the Euclid run.
    #[must_use]
    pub fn inverse(&self) -> Option<(Element, InverseCertificate)> {
        if self.is_zero() {
            return None;
        }
        let (gcd, cofactor, _) = poly_ext_gcd(&self.coeffs, &self.field.minpoly);
        if poly_degree(&gcd) != Some(0) {
            return None;
        }
        let inverse = self.field.element(&cofactor);
        let certificate = InverseCertificate {
            minpoly: self.field.minpoly.clone(),
            element: self.coeffs.clone(),
            inverse: inverse.coeffs.clone(),
        };
        Some((inverse, certificate))
    }

    /// The field norm and trace of this element, with a certificate.
    ///
    /// Both are read off the characteristic polynomial of the multiplication
    /// matrix: `norm = (−1)ⁿ χ(0)` and `trace = −χ_{n−1}`. The certificate's
    /// `verify` re-derives the matrix, re-checks `χ` by Cayley–Hamilton, and
    /// then re-derives the norm and trace a **second** way — determinant by
    /// elimination and the matrix trace — so the two routes must agree.
    #[must_use]
    pub fn norm_trace(&self) -> NormTraceCertificate {
        let matrix = self.multiplication_matrix();
        let char_poly = char_poly_faddeev(&matrix);
        let degree = matrix.len();
        let sign = if degree.is_multiple_of(2) {
            rat_one()
        } else {
            -rat_one()
        };
        let norm = &sign * &char_poly[0];
        let trace = if degree == 0 {
            rat_zero()
        } else {
            -char_poly[degree - 1].clone()
        };
        NormTraceCertificate {
            minpoly: self.field.minpoly.clone(),
            element: self.coeffs.clone(),
            matrix,
            char_poly,
            norm,
            trace,
        }
    }

    /// The field norm. `uncertified` convenience view of
    /// [`Element::norm_trace`], which is the certified route.
    #[must_use]
    pub fn norm(&self) -> BigRational {
        self.norm_trace().norm
    }

    /// The field trace. `uncertified` convenience view of
    /// [`Element::norm_trace`], which is the certified route.
    #[must_use]
    pub fn trace(&self) -> BigRational {
        self.norm_trace().trace
    }

    /// The minimal polynomial of this element over ℚ, with a certificate.
    ///
    /// Found by locating the first power `self^k` that lies in the ℚ-span of
    /// the lower powers and solving for the dependency. Returns `None` only
    /// when the field is degenerate.
    #[must_use]
    pub fn minimal_polynomial(&self) -> Option<(Vec<BigRational>, ElementMinPolyCertificate)> {
        let degree = self.field.degree();
        if degree == 0 {
            return None;
        }
        let mut powers: Vec<Vec<BigRational>> = Vec::new();
        let mut current = self.field.one();
        for _ in 0..=degree {
            powers.push(current.coeffs.clone());
            current = current.mul(self)?;
        }
        // Find the smallest k with powers[k] in span(powers[0..k]).
        for k in 1..=degree {
            if let Some(solution) = solve_dependency(&powers[..k], &powers[k]) {
                let mut poly: Vec<BigRational> = solution.iter().map(core::ops::Neg::neg).collect();
                poly.push(rat_one());
                let poly = poly_trim(poly);
                let certificate = ElementMinPolyCertificate {
                    minpoly: self.field.minpoly.clone(),
                    element: self.coeffs.clone(),
                    poly: poly.clone(),
                };
                return Some((poly, certificate));
            }
        }
        None
    }
}

/// Solve `target = sum_j c_j * basis[j]` over ℚ, or `None` if `target` is not
/// in the span. Gaussian elimination on the transposed system.
fn solve_dependency(
    basis: &[Vec<BigRational>],
    target: &[BigRational],
) -> Option<Vec<BigRational>> {
    let rows = target.len();
    let cols = basis.len();
    let mut augmented: Vec<Vec<BigRational>> = (0..rows)
        .map(|row| {
            let mut line: Vec<BigRational> = (0..cols).map(|col| basis[col][row].clone()).collect();
            line.push(target[row].clone());
            line
        })
        .collect();
    let mut pivot_of_col = vec![usize::MAX; cols];
    let mut pivot_row = 0usize;
    for col in 0..cols {
        let Some(found) = (pivot_row..rows).find(|&row| !augmented[row][col].is_zero()) else {
            continue;
        };
        augmented.swap(found, pivot_row);
        let inverse = augmented[pivot_row][col].clone().recip();
        for entry in &mut augmented[pivot_row] {
            *entry *= &inverse;
        }
        let pivot_values = augmented[pivot_row].clone();
        for (row, line) in augmented.iter_mut().enumerate().take(rows) {
            if row == pivot_row || line[col].is_zero() {
                continue;
            }
            let factor = line[col].clone();
            for (index, pivot_value) in pivot_values.iter().enumerate().skip(col) {
                let term = &factor * pivot_value;
                line[index] -= term;
            }
        }
        pivot_of_col[col] = pivot_row;
        pivot_row += 1;
    }
    // Inconsistent if some row is 0 = nonzero.
    for row in augmented.iter().take(rows) {
        if row[..cols].iter().all(num_traits::Zero::is_zero) && !row[cols].is_zero() {
            return None;
        }
    }
    let mut solution = vec![rat_zero(); cols];
    for (col, &row) in pivot_of_col.iter().enumerate() {
        if row != usize::MAX {
            solution[col] = augmented[row][cols].clone();
        }
    }
    Some(solution)
}

// ---------------------------------------------------------------------------
// Certificates over a number field
// ---------------------------------------------------------------------------

/// `a · a⁻¹ ≡ 1 (mod f)`, checkable by re-multiplying and reducing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InverseCertificate {
    /// The field's monic minimal polynomial, least-significant-first.
    pub minpoly: Vec<BigRational>,
    /// The element, in the power basis.
    pub element: Vec<BigRational>,
    /// The claimed inverse, in the power basis.
    pub inverse: Vec<BigRational>,
}

impl InverseCertificate {
    /// Re-derive `a · a⁻¹ ≡ 1 (mod f)` from the recorded data alone.
    ///
    /// # Errors
    ///
    /// [`CertificateError::DegreeMismatch`] if either vector is not the field
    /// degree long, [`CertificateError::ZeroIsNotInvertible`] for a zero
    /// element, and [`CertificateError::NotAnInverse`] naming the first
    /// coefficient at which the reduced product differs from `1`.
    pub fn verify(&self) -> Result<(), CertificateError> {
        let degree = poly_degree(&self.minpoly).ok_or(CertificateError::ModulusDegenerate)?;
        // I1: shape.
        if self.element.len() != degree {
            return Err(CertificateError::DegreeMismatch {
                expected: degree,
                found: self.element.len(),
            });
        }
        if self.inverse.len() != degree {
            return Err(CertificateError::DegreeMismatch {
                expected: degree,
                found: self.inverse.len(),
            });
        }
        // I2: the zero element has no inverse, and 0 * anything reduces to 0,
        // so without this guard a zero/zero pair would be caught by I3 only
        // for a nonzero claimed inverse.
        if self.element.iter().all(num_traits::Zero::is_zero) {
            return Err(CertificateError::ZeroIsNotInvertible);
        }
        // I3: the identity itself, re-multiplied and reduced.
        let product = poly_mul(&self.element, &self.inverse);
        let (_, remainder) =
            poly_divrem(&product, &self.minpoly).ok_or(CertificateError::ModulusDegenerate)?;
        for index in 0..degree {
            let got = remainder.get(index).cloned().unwrap_or_else(rat_zero);
            let want = if index == 0 { rat_one() } else { rat_zero() };
            if got != want {
                return Err(CertificateError::NotAnInverse { degree: index });
            }
        }
        if remainder.len() > degree {
            return Err(CertificateError::NotAnInverse { degree });
        }
        Ok(())
    }
}

/// The norm and trace of an element, backed by the characteristic polynomial
/// of its multiplication matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormTraceCertificate {
    /// The field's monic minimal polynomial, least-significant-first.
    pub minpoly: Vec<BigRational>,
    /// The element, in the power basis.
    pub element: Vec<BigRational>,
    /// The multiplication matrix, row-major.
    pub matrix: Vec<Vec<BigRational>>,
    /// The characteristic polynomial of `matrix`, least-significant-first,
    /// monic of degree `n`.
    pub char_poly: Vec<BigRational>,
    /// The claimed norm.
    pub norm: BigRational,
    /// The claimed trace.
    pub trace: BigRational,
}

impl NormTraceCertificate {
    /// The claimed norm.
    #[must_use]
    pub fn norm(&self) -> &BigRational {
        &self.norm
    }

    /// The claimed trace.
    #[must_use]
    pub fn trace(&self) -> &BigRational {
        &self.trace
    }

    /// Re-derive the norm and trace two independent ways and require both to
    /// agree with the recorded values.
    ///
    /// # Errors
    ///
    /// [`CertificateError::MultiplicationMatrixMismatch`] naming the first bad
    /// entry, [`CertificateError::CharPolyNotMonic`],
    /// [`CertificateError::CayleyHamiltonFailed`],
    /// [`CertificateError::NormNotCharPolyConstant`],
    /// [`CertificateError::TraceNotCharPolySubleading`],
    /// [`CertificateError::NormNotDeterminant`], or
    /// [`CertificateError::TraceNotMatrixTrace`].
    pub fn verify(&self) -> Result<(), CertificateError> {
        let field = NumberField::new(&self.minpoly)?;
        let degree = field.degree();
        if self.element.len() != degree {
            return Err(CertificateError::DegreeMismatch {
                expected: degree,
                found: self.element.len(),
            });
        }
        // N1: the matrix is the one the element and modulus determine.
        let rebuilt = field.element(&self.element).multiplication_matrix();
        if self.matrix.len() != degree {
            return Err(CertificateError::MultiplicationMatrixMismatch { row: 0, col: 0 });
        }
        for (row, line) in rebuilt.iter().enumerate() {
            if self.matrix[row].len() != degree {
                return Err(CertificateError::MultiplicationMatrixMismatch { row, col: 0 });
            }
            for (col, entry) in line.iter().enumerate() {
                if &self.matrix[row][col] != entry {
                    return Err(CertificateError::MultiplicationMatrixMismatch { row, col });
                }
            }
        }
        // N2: chi is monic of degree n.
        if self.char_poly.len() != degree + 1 || !self.char_poly[degree].is_one() {
            return Err(CertificateError::CharPolyNotMonic);
        }
        // N3: chi really is the characteristic polynomial of this matrix.
        if !matrix_poly_is_zero(&self.char_poly, &self.matrix) {
            return Err(CertificateError::CayleyHamiltonFailed);
        }
        // N4: norm read off the constant term.
        let sign = if degree.is_multiple_of(2) {
            rat_one()
        } else {
            -rat_one()
        };
        if self.norm != &sign * &self.char_poly[0] {
            return Err(CertificateError::NormNotCharPolyConstant);
        }
        // N5: trace read off the subleading coefficient.
        if self.trace != -self.char_poly[degree - 1].clone() {
            return Err(CertificateError::TraceNotCharPolySubleading);
        }
        // N6: norm again, this time as a determinant by elimination.
        if self.norm != matrix_determinant(&self.matrix) {
            return Err(CertificateError::NormNotDeterminant);
        }
        // N7: trace again, this time as the sum of the diagonal.
        if self.trace != matrix_trace(&self.matrix) {
            return Err(CertificateError::TraceNotMatrixTrace);
        }
        Ok(())
    }
}

/// The minimal polynomial of an element of a [`NumberField`] over ℚ.
///
/// Three guards *define* the object: monic, annihilating, irreducible. A monic
/// irreducible polynomial that the element satisfies is the minimal
/// polynomial, so no separate minimality guard is shipped — one would be a
/// guard no forgery could reach.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElementMinPolyCertificate {
    /// The field's monic minimal polynomial, least-significant-first.
    pub minpoly: Vec<BigRational>,
    /// The element, in the power basis.
    pub element: Vec<BigRational>,
    /// The claimed minimal polynomial of the element, least-significant-first.
    pub poly: Vec<BigRational>,
}

impl ElementMinPolyCertificate {
    /// The claimed minimal polynomial.
    #[must_use]
    pub fn polynomial(&self) -> &[BigRational] {
        &self.poly
    }

    /// Re-derive the three defining properties.
    ///
    /// # Errors
    ///
    /// [`CertificateError::MinimalPolynomialNotMonic`],
    /// [`CertificateError::MinimalPolynomialNotSatisfied`],
    /// [`CertificateError::MinimalPolynomialReducible`], or
    /// [`CertificateError::IrreducibilityUndecided`] when the reused
    /// factorizer declines.
    pub fn verify(&self) -> Result<(), CertificateError> {
        let field = NumberField::new(&self.minpoly)?;
        // M1: monic and non-constant.
        let degree = poly_degree(&self.poly).ok_or(CertificateError::MinimalPolynomialNotMonic)?;
        if degree == 0 || !self.poly[degree].is_one() || self.poly.len() != degree + 1 {
            return Err(CertificateError::MinimalPolynomialNotMonic);
        }
        // M2: the element satisfies it, evaluated in the field by Horner.
        let element = field.element(&self.element);
        let mut accumulator = field.zero();
        for coefficient in self.poly.iter().rev() {
            accumulator = accumulator
                .mul(&element)
                .ok_or(CertificateError::FieldMismatch)?;
            accumulator = accumulator
                .add(&field.rational(coefficient))
                .ok_or(CertificateError::FieldMismatch)?;
        }
        if !accumulator.is_zero() {
            return Err(CertificateError::MinimalPolynomialNotSatisfied);
        }
        // M3: irreducible over Q.
        match is_irreducible_over_q(&self.poly) {
            None => Err(CertificateError::IrreducibilityUndecided),
            Some(false) => Err(CertificateError::MinimalPolynomialReducible),
            Some(true) => Ok(()),
        }
    }
}

// ---------------------------------------------------------------------------
// Gaussian integers
// ---------------------------------------------------------------------------

/// An element of `ℤ[i]`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct GaussianInt {
    /// The real part.
    pub re: BigInt,
    /// The imaginary part.
    pub im: BigInt,
}

impl fmt::Display for GaussianInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.im.is_negative() {
            write!(f, "{}{}i", self.re, self.im)
        } else {
            write!(f, "{}+{}i", self.re, self.im)
        }
    }
}

impl GaussianInt {
    /// Build `re + im·i`.
    #[must_use]
    pub fn new(re: BigInt, im: BigInt) -> GaussianInt {
        GaussianInt { re, im }
    }

    /// Build `re + im·i` from small integers.
    #[must_use]
    pub fn from_i64(re: i64, im: i64) -> GaussianInt {
        GaussianInt::new(BigInt::from(re), BigInt::from(im))
    }

    /// `0`.
    #[must_use]
    pub fn zero() -> GaussianInt {
        GaussianInt::from_i64(0, 0)
    }

    /// `1`.
    #[must_use]
    pub fn one() -> GaussianInt {
        GaussianInt::from_i64(1, 0)
    }

    /// `i`.
    #[must_use]
    pub fn imaginary_unit() -> GaussianInt {
        GaussianInt::from_i64(0, 1)
    }

    /// Whether this is `0`.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.re.is_zero() && self.im.is_zero()
    }

    /// The field norm `re² + im²`, always non-negative.
    #[must_use]
    pub fn norm(&self) -> BigInt {
        &self.re * &self.re + &self.im * &self.im
    }

    /// Complex conjugate. `uncertified`.
    #[must_use]
    pub fn conj(&self) -> GaussianInt {
        GaussianInt::new(self.re.clone(), -self.im.clone())
    }

    /// Sum. `uncertified`.
    #[must_use]
    pub fn add(&self, other: &GaussianInt) -> GaussianInt {
        GaussianInt::new(&self.re + &other.re, &self.im + &other.im)
    }

    /// Difference. `uncertified`.
    #[must_use]
    pub fn sub(&self, other: &GaussianInt) -> GaussianInt {
        GaussianInt::new(&self.re - &other.re, &self.im - &other.im)
    }

    /// Negation. `uncertified`.
    #[must_use]
    pub fn neg(&self) -> GaussianInt {
        GaussianInt::new(-self.re.clone(), -self.im.clone())
    }

    /// Product. `uncertified`.
    #[must_use]
    pub fn mul(&self, other: &GaussianInt) -> GaussianInt {
        GaussianInt::new(
            &self.re * &other.re - &self.im * &other.im,
            &self.re * &other.im + &self.im * &other.re,
        )
    }

    /// Whether this is one of the four units `1, −1, i, −i`.
    #[must_use]
    pub fn is_unit(&self) -> bool {
        self.norm().is_one()
    }

    /// Euclidean division: `(q, r)` with `self = q·other + r` and
    /// `N(r) ≤ N(other)/2 < N(other)`. `None` exactly when `other` is `0`.
    #[must_use]
    pub fn divmod(&self, other: &GaussianInt) -> Option<(GaussianInt, GaussianInt)> {
        if other.is_zero() {
            return None;
        }
        let denominator = other.norm();
        let numerator = self.mul(&other.conj());
        let quotient = GaussianInt::new(
            round_div(&numerator.re, &denominator),
            round_div(&numerator.im, &denominator),
        );
        let remainder = self.sub(&quotient.mul(other));
        Some((quotient, remainder))
    }

    /// Exact quotient, or `None` when `other` does not divide `self` (or is
    /// `0`).
    #[must_use]
    pub fn exact_div(&self, other: &GaussianInt) -> Option<GaussianInt> {
        let (quotient, remainder) = self.divmod(other)?;
        remainder.is_zero().then_some(quotient)
    }

    /// Greatest common divisor by the Euclidean algorithm, returned in its
    /// canonical associate (`re > 0` and `im ≥ 0`).
    ///
    /// `gcd(0, 0)` is `0`.
    #[must_use]
    pub fn gcd(&self, other: &GaussianInt) -> GaussianInt {
        let mut left = self.clone();
        let mut right = other.clone();
        while !right.is_zero() {
            let Some((_, remainder)) = left.divmod(&right) else {
                break;
            };
            left = right;
            right = remainder;
        }
        left.canonical_associate()
    }

    /// The unique associate with `re > 0` and `im ≥ 0`; `0` maps to `0`.
    ///
    /// Determinism: this is what makes a factor list canonical.
    #[must_use]
    pub fn canonical_associate(&self) -> GaussianInt {
        if self.is_zero() {
            return GaussianInt::zero();
        }
        let mut current = self.clone();
        for _ in 0..4 {
            if current.re.is_positive() && !current.im.is_negative() {
                return current;
            }
            current = current.mul(&GaussianInt::imaginary_unit());
        }
        current
    }

    /// Whether this is a Gaussian prime: prime norm, or an inert rational
    /// prime `≡ 3 (mod 4)` up to a unit.
    ///
    /// `None` when the magnitude is past the `i128` primality routine the test
    /// reuses; the caller must treat that as "not decided", never as `false`.
    #[must_use]
    pub fn is_gaussian_prime(&self) -> Option<bool> {
        let norm = self.norm();
        let norm_small = i128::try_from(&norm).ok()?;
        if is_prime(norm_small) {
            return Some(true);
        }
        // Inert case: an associate of a rational prime p = 3 (mod 4), whose
        // norm is p^2.
        let canonical = self.canonical_associate();
        if !canonical.im.is_zero() {
            return Some(false);
        }
        let value = i128::try_from(&canonical.re).ok()?;
        Some(is_prime(value) && value.rem_euclid(4) == 3)
    }

    /// Factor into Gaussian primes times a unit.
    ///
    /// The rational primes dividing `N(self)` come from
    /// [`crate::ntheory::factorize`]; a prime `p ≡ 1 (mod 4)` is split as
    /// `gcd(p, s + i)` where `s² ≡ −1 (mod p)` comes from Tonelli–Shanks
    /// ([`crate::ntheory_advanced::sqrt_mod`]).
    ///
    /// # Errors
    ///
    /// [`DeclineReason::ZeroInput`] for `0`,
    /// [`DeclineReason::MagnitudeOutOfRange`] when `N(self)` exceeds the
    /// `i128` factorizer, [`DeclineReason::SqrtModDeclined`] if Tonelli–Shanks
    /// declines, and [`DeclineReason::FactorizationIncomplete`] if the residue
    /// after dividing everything out is not a unit.
    pub fn factor(&self) -> Result<GaussianFactorizationCertificate, DeclineReason> {
        if self.is_zero() {
            return Err(DeclineReason::ZeroInput);
        }
        let norm = self.norm();
        let norm_small = i128::try_from(&norm).map_err(|_| DeclineReason::MagnitudeOutOfRange)?;
        let rational_primes = factorize(norm_small);
        let mut current = self.clone();
        let mut factors: Vec<GaussianInt> = Vec::new();
        for (prime, _) in rational_primes {
            let candidates: Vec<GaussianInt> = if prime == 2 {
                vec![GaussianInt::from_i64(1, 1)]
            } else if prime.rem_euclid(4) == 3 {
                vec![GaussianInt::new(BigInt::from(prime), BigInt::zero())]
            } else {
                let root =
                    sqrt_mod(prime - 1, prime).ok_or(DeclineReason::SqrtModDeclined { prime })?;
                let splitter = GaussianInt::new(BigInt::from(prime), BigInt::zero())
                    .gcd(&GaussianInt::new(BigInt::from(root), BigInt::one()));
                let conjugate = splitter.conj().canonical_associate();
                vec![splitter, conjugate]
            };
            for candidate in candidates {
                while let Some(quotient) = current.exact_div(&candidate) {
                    factors.push(candidate.clone());
                    current = quotient;
                }
            }
        }
        if !current.is_unit() {
            return Err(DeclineReason::FactorizationIncomplete);
        }
        factors.sort_by(|left, right| {
            left.norm()
                .cmp(&right.norm())
                .then_with(|| left.re.cmp(&right.re))
                .then_with(|| left.im.cmp(&right.im))
        });
        Ok(GaussianFactorizationCertificate {
            value: self.clone(),
            unit: current,
            factors,
        })
    }
}

/// Round `numerator / denominator` to a nearest integer (`denominator > 0`),
/// with an error of at most one half.
fn round_div(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    let doubled = numerator * 2 + denominator;
    let twice = denominator * 2;
    // Floor division: `BigInt`'s `/` truncates toward zero, so correct.
    let mut quotient: BigInt = &doubled / &twice;
    let product: BigInt = &quotient * &twice;
    let residue: BigInt = &doubled - &product;
    if residue.is_negative() {
        quotient -= BigInt::one();
    }
    quotient
}

/// A factorization of a nonzero Gaussian integer into Gaussian primes times a
/// unit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GaussianFactorizationCertificate {
    /// The value being factored.
    pub value: GaussianInt,
    /// The leftover unit, one of `1, −1, i, −i`.
    pub unit: GaussianInt,
    /// The Gaussian prime factors with multiplicity, sorted by
    /// `(norm, re, im)`.
    pub factors: Vec<GaussianInt>,
}

impl GaussianFactorizationCertificate {
    /// Re-derive the factorization from the recorded data alone.
    ///
    /// # Errors
    ///
    /// [`CertificateError::ZeroHasNoFactorization`],
    /// [`CertificateError::NotAGaussianUnit`],
    /// [`CertificateError::GaussianProductMismatch`],
    /// [`CertificateError::NotAGaussianPrime`] naming the offending index, or
    /// [`CertificateError::MagnitudeOutOfRange`] when a factor's norm is past
    /// the reused `i128` primality test.
    pub fn verify(&self) -> Result<(), CertificateError> {
        // G1: zero has no factorization at all.
        if self.value.is_zero() {
            return Err(CertificateError::ZeroHasNoFactorization);
        }
        // G2: the unit is a unit.
        if !self.unit.is_unit() {
            return Err(CertificateError::NotAGaussianUnit);
        }
        // G3: the product identity.
        let mut product = self.unit.clone();
        for factor in &self.factors {
            product = product.mul(factor);
        }
        if product != self.value {
            return Err(CertificateError::GaussianProductMismatch);
        }
        // G4: every factor really is a Gaussian prime. This also rejects a
        // padded unit factor, whose norm is 1.
        for (index, factor) in self.factors.iter().enumerate() {
            match factor.is_gaussian_prime() {
                None => return Err(CertificateError::MagnitudeOutOfRange),
                Some(false) => return Err(CertificateError::NotAGaussianPrime { index }),
                Some(true) => {}
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Sums of two squares
// ---------------------------------------------------------------------------

/// Either a representation `n = a² + b²` or a refutation of one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TwoSquaresCertificate {
    /// `n = a² + b²`, with `a, b ≥ 0`.
    Represented {
        /// The number represented.
        n: BigInt,
        /// One square root summand.
        a: BigInt,
        /// The other square root summand.
        b: BigInt,
    },
    /// `n` is not a sum of two squares: the named prime is `≡ 3 (mod 4)` and
    /// occurs to odd multiplicity.
    Refuted {
        /// The number refuted.
        n: BigInt,
        /// The full prime factorization of `n`, with Pratt certificates.
        factorization: FactorizationCertificate,
        /// The obstructing prime, `≡ 3 (mod 4)`.
        prime: i128,
        /// Its multiplicity in `n`, which must be odd.
        exponent: u32,
    },
}

impl TwoSquaresCertificate {
    /// Re-derive the claim from the recorded data alone, in whichever
    /// direction the certificate points.
    ///
    /// # Errors
    ///
    /// Representation: [`CertificateError::NegativeSumOfSquares`] or
    /// [`CertificateError::SumOfSquaresMismatch`]. Refutation:
    /// [`CertificateError::MagnitudeOutOfRange`],
    /// [`CertificateError::FactorizationCertificateInvalid`],
    /// [`CertificateError::RefutationExponentNotInFactorization`],
    /// [`CertificateError::RefutationPrimeNotThreeModFour`], or
    /// [`CertificateError::RefutationExponentEven`].
    pub fn verify(&self) -> Result<(), CertificateError> {
        match self {
            TwoSquaresCertificate::Represented { n, a, b } => {
                // R1: a sum of two squares is never negative, so a negative n
                // is refused before the arithmetic even runs.
                if n.is_negative() {
                    return Err(CertificateError::NegativeSumOfSquares);
                }
                // R2: the identity, recomputed exactly.
                if a * a + b * b != *n {
                    return Err(CertificateError::SumOfSquaresMismatch);
                }
                Ok(())
            }
            TwoSquaresCertificate::Refuted {
                n,
                factorization,
                prime,
                exponent,
            } => {
                let small = i128::try_from(n).map_err(|_| CertificateError::MagnitudeOutOfRange)?;
                // F1: the attached factorization really is the factorization
                // of n, Pratt certificates and all.
                if !check_factorization_certificate(small, factorization) {
                    return Err(CertificateError::FactorizationCertificateInvalid);
                }
                // F2: the named (prime, exponent) pair occurs in it.
                if !factorization
                    .factors
                    .iter()
                    .any(|&(base, power)| base == *prime && power == *exponent)
                {
                    return Err(CertificateError::RefutationExponentNotInFactorization);
                }
                // F3: only a prime = 3 (mod 4) is an obstruction.
                if prime.rem_euclid(4) != 3 {
                    return Err(CertificateError::RefutationPrimeNotThreeModFour);
                }
                // F4: only an odd exponent is an obstruction.
                if exponent % 2 == 0 {
                    return Err(CertificateError::RefutationExponentEven);
                }
                Ok(())
            }
        }
    }
}

/// What [`two_squares_outcome`] concluded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TwoSquaresOutcome {
    /// A checkable answer, in one direction or the other.
    Decided(TwoSquaresCertificate),
    /// The producer declined, with a named reason. Never a claim about `n`.
    Declined(DeclineReason),
}

/// Represent `n` as a sum of two squares, or refute that it is one.
///
/// This is the [`Option`] view of [`two_squares_outcome`]: a decline and a
/// negative input both come back as `None`, so use
/// [`two_squares_outcome`] when the difference matters.
#[must_use]
pub fn two_squares(n: &BigInt) -> Option<TwoSquaresCertificate> {
    match two_squares_outcome(n) {
        TwoSquaresOutcome::Decided(certificate) => Some(certificate),
        TwoSquaresOutcome::Declined(_) => None,
    }
}

/// Represent `n` as a sum of two squares, refute that it is one, or decline
/// with a named reason.
///
/// The factorization comes from [`crate::ntheory::factorize`]; a refutation
/// additionally carries the Pratt-backed
/// [`crate::ntheory_certify::certify_factorization`], and declines with
/// [`DeclineReason::PrattCertificationTooExpensive`] above
/// [`PRATT_CERTIFY_BOUND`] rather than assert the refutation unbacked.
#[must_use]
pub fn two_squares_outcome(n: &BigInt) -> TwoSquaresOutcome {
    if n.is_negative() {
        return TwoSquaresOutcome::Declined(DeclineReason::NegativeInput);
    }
    if n.is_zero() {
        return TwoSquaresOutcome::Decided(TwoSquaresCertificate::Represented {
            n: BigInt::zero(),
            a: BigInt::zero(),
            b: BigInt::zero(),
        });
    }
    let Ok(small) = i128::try_from(n) else {
        return TwoSquaresOutcome::Declined(DeclineReason::MagnitudeOutOfRange);
    };
    let factors = factorize(small);
    if factors.is_empty() && small != 1 {
        return TwoSquaresOutcome::Declined(DeclineReason::FactorizationDeclined);
    }
    // A prime = 3 (mod 4) to odd multiplicity is the whole obstruction.
    if let Some(&(prime, exponent)) = factors
        .iter()
        .find(|&&(base, power)| base.rem_euclid(4) == 3 && power % 2 == 1)
    {
        if small > PRATT_CERTIFY_BOUND {
            return TwoSquaresOutcome::Declined(DeclineReason::PrattCertificationTooExpensive {
                bound: PRATT_CERTIFY_BOUND,
            });
        }
        let Some(factorization) = certify_factorization(small) else {
            return TwoSquaresOutcome::Declined(DeclineReason::FactorizationDeclined);
        };
        return TwoSquaresOutcome::Decided(TwoSquaresCertificate::Refuted {
            n: n.clone(),
            factorization,
            prime,
            exponent,
        });
    }
    // Otherwise build a Gaussian integer of norm n and read off its parts.
    let mut witness = GaussianInt::one();
    for (prime, exponent) in factors {
        let piece = if prime == 2 {
            GaussianInt::from_i64(1, 1)
        } else if prime.rem_euclid(4) == 3 {
            GaussianInt::new(BigInt::from(prime), BigInt::zero())
        } else {
            let Some(root) = sqrt_mod(prime - 1, prime) else {
                return TwoSquaresOutcome::Declined(DeclineReason::SqrtModDeclined { prime });
            };
            GaussianInt::new(BigInt::from(prime), BigInt::zero())
                .gcd(&GaussianInt::new(BigInt::from(root), BigInt::one()))
        };
        // An inert prime contributes p^(e/2), which is why the exponent is
        // halved exactly in the p = 3 (mod 4) branch.
        let power = if prime.rem_euclid(4) == 3 {
            exponent / 2
        } else {
            exponent
        };
        for _ in 0..power {
            witness = witness.mul(&piece);
        }
    }
    TwoSquaresOutcome::Decided(TwoSquaresCertificate::Represented {
        n: n.clone(),
        a: witness.re.abs(),
        b: witness.im.abs(),
    })
}

// ---------------------------------------------------------------------------
// Quadratic fields
// ---------------------------------------------------------------------------

/// `ℚ(√d)` for a squarefree `d ∉ {0, 1}`, presented as `ℚ[x]/(x² − d)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuadraticField {
    radicand: BigInt,
    field: NumberField,
}

impl QuadraticField {
    /// Build `ℚ(√d)`.
    ///
    /// # Errors
    ///
    /// [`CertificateError::RadicandNotAdmissible`] when `d` is `0`, `±1`, not
    /// squarefree, or past the `i128` range of the reused squarefree test;
    /// and whatever [`NumberField::new`] refuses `x² − d` with.
    pub fn new(radicand: &BigInt) -> Result<QuadraticField, CertificateError> {
        if radicand.is_zero() || radicand.abs().is_one() {
            return Err(CertificateError::RadicandNotAdmissible);
        }
        let small = i128::try_from(radicand).map_err(|_| CertificateError::MagnitudeOutOfRange)?;
        if !crate::ntheory_more::is_squarefree(small.abs()) {
            return Err(CertificateError::RadicandNotAdmissible);
        }
        let minpoly = vec![
            -BigRational::from_integer(radicand.clone()),
            rat_zero(),
            rat_one(),
        ];
        let field = NumberField::new(&minpoly)?;
        Ok(QuadraticField {
            radicand: radicand.clone(),
            field,
        })
    }

    /// The squarefree `d`.
    #[must_use]
    pub fn radicand(&self) -> &BigInt {
        &self.radicand
    }

    /// The underlying [`NumberField`] `ℚ[x]/(x² − d)`.
    #[must_use]
    pub fn as_number_field(&self) -> &NumberField {
        &self.field
    }

    /// The element `a + b√d`.
    #[must_use]
    pub fn element(&self, a: &BigRational, b: &BigRational) -> Element {
        self.field.element(&[a.clone(), b.clone()])
    }

    /// The norm form `a² − d b²`. `uncertified`; it is one multiplication, and
    /// [`Element::norm_trace`] is the certified route through the field.
    #[must_use]
    pub fn norm_form(&self, a: &BigInt, b: &BigInt) -> BigInt {
        a * a - &self.radicand * b * b
    }

    /// Whether `a + b√d` is a unit of `ℤ[√d]`, i.e. `|a² − d b²| = 1`.
    ///
    /// Note this is `ℤ[√d]`, **not** the ring of integers: for `d ≡ 1 (mod 4)`
    /// the maximal order `ℤ[(1+√d)/2]` is strictly larger and may contain
    /// smaller units. Out of scope for this slice.
    #[must_use]
    pub fn is_unit(&self, a: &BigInt, b: &BigInt) -> bool {
        self.norm_form(a, b).abs().is_one()
    }

    /// The fundamental unit of `ℤ[√d]` for positive non-square `d`, with a
    /// certificate.
    ///
    /// Found by walking the convergents of the continued fraction of `√d` — the
    /// expansion itself comes from
    /// [`crate::ntheory_advanced::sqrt_continued_fraction`], the recurrence is
    /// re-run here in [`BigInt`] — and taking the first with `a² − d b² = ±1`.
    ///
    /// The *unit* claim is certified. The *fundamental* claim is certified
    /// only when `b ≤` [`MINIMALITY_SEARCH_BOUND`]; above that it is labelled
    /// [`Minimality::Uncertified`], because the exhaustive search that would
    /// prove it is `b` iterations and `d = 61` has `b = 226_153_980`.
    ///
    /// # Errors
    ///
    /// [`DeclineReason::NotRealQuadratic`] if `d ≤ 1` or is a perfect square
    /// (the continued fraction terminates), [`DeclineReason::MagnitudeOutOfRange`]
    /// if `d` is past the `i128` continued-fraction routine, and
    /// [`DeclineReason::NoUnitFound`] if no convergent in two full periods is a
    /// unit.
    pub fn fundamental_unit(&self) -> Result<FundamentalUnitCertificate, DeclineReason> {
        let (a, b, norm) = self.convergent_unit(|value| value.abs().is_one())?;
        let minimality = match u64::try_from(&b) {
            Ok(bound) if bound <= MINIMALITY_SEARCH_BOUND => Minimality::ExhaustiveBelow {
                searched: bound - 1,
            },
            _ => Minimality::Uncertified {
                reason: format!(
                    "b exceeds MINIMALITY_SEARCH_BOUND ({MINIMALITY_SEARCH_BOUND}); minimality \
                     rests on the classical theorem that every unit of Z[sqrt d] with a, b > 0 \
                     appears among the convergents of sqrt d, which this module does not check"
                ),
            },
        };
        Ok(FundamentalUnitCertificate {
            radicand: self.radicand.clone(),
            a,
            b,
            norm,
            minimality,
        })
    }

    /// The fundamental solution of the Pell equation `x² − d y² = 1`, as a unit
    /// certificate.
    ///
    /// This is the fundamental unit when that has norm `+1`, and its **square**
    /// when the fundamental unit has norm `−1` — `d = 2` and `d = 61` are both
    /// of the second kind, which is why `d = 61` gives `1766319049 +
    /// 226153980√61` here but `29718 + 3805√61` from
    /// [`QuadraticField::fundamental_unit`].
    ///
    /// The unit claim is certified. The *fundamental* claim is always labelled
    /// [`Minimality::Uncertified`], because minimality here is relative to norm
    /// `+1` while this module's search covers norm `±1` and would report the
    /// smaller norm-`−1` unit as a counterexample.
    ///
    /// # Errors
    ///
    /// The same declines as [`QuadraticField::fundamental_unit`].
    pub fn pell_unit(&self) -> Result<FundamentalUnitCertificate, DeclineReason> {
        let (a, b, norm) = self.convergent_unit(num_traits::One::is_one)?;
        Ok(FundamentalUnitCertificate {
            radicand: self.radicand.clone(),
            a,
            b,
            norm,
            minimality: Minimality::Uncertified {
                reason: "minimality here is relative to norm +1, while the search this \
                         certificate would run covers norm +-1 and would report the smaller \
                         norm -1 unit as a counterexample; use fundamental_unit for the \
                         certified-minimal object"
                    .to_string(),
            },
        })
    }

    /// Walk the convergents of `√d` and return the first `(a, b, norm)` whose
    /// norm the predicate accepts.
    fn convergent_unit(
        &self,
        accept: impl Fn(&BigInt) -> bool,
    ) -> Result<(BigInt, BigInt, BigInt), DeclineReason> {
        if !self.radicand.is_positive() {
            return Err(DeclineReason::NotRealQuadratic);
        }
        let small =
            i128::try_from(&self.radicand).map_err(|_| DeclineReason::MagnitudeOutOfRange)?;
        let (head, period) =
            sqrt_continued_fraction(small).ok_or(DeclineReason::NotRealQuadratic)?;
        // Two full periods always reach the fundamental solution of
        // `x^2 - d y^2 = 1`, whether the period length is even or odd.
        let mut terms = vec![BigInt::from(head)];
        for _ in 0..2 {
            terms.extend(period.iter().map(|&term| BigInt::from(term)));
        }
        // Convergent recurrence in BigInt: h_k = a_k h_{k-1} + h_{k-2}, seeded
        // with h_{-1} = 1, h_{-2} = 0 and k_{-1} = 0, k_{-2} = 1.
        let mut num_prev = BigInt::zero();
        let mut num_curr = BigInt::one();
        let mut den_prev = BigInt::one();
        let mut den_curr = BigInt::zero();
        for term in &terms {
            let num_next = term * &num_curr + &num_prev;
            let den_next = term * &den_curr + &den_prev;
            num_prev = core::mem::replace(&mut num_curr, num_next);
            den_prev = core::mem::replace(&mut den_curr, den_next);
            if !den_curr.is_positive() {
                continue;
            }
            let norm = self.norm_form(&num_curr, &den_curr);
            if accept(&norm) {
                return Ok((num_curr.clone(), den_curr.clone(), norm));
            }
        }
        Err(DeclineReason::NoUnitFound)
    }
}

/// Whether a [`FundamentalUnitCertificate`]'s *fundamental* claim was proved,
/// or only labelled.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Minimality {
    /// Every `1 ≤ y < b` was examined and none gives a unit, so the recorded
    /// unit is the smallest. `verify` re-runs the whole search.
    ExhaustiveBelow {
        /// The number of `y` values the search covered; must equal `b − 1`.
        searched: u64,
    },
    /// The search was not run. The unit claim still holds; *fundamental* is
    /// labelled, never promoted.
    Uncertified {
        /// Why the search was skipped.
        reason: String,
    },
}

/// A unit `a + b√d` of `ℤ[√d]`, claimed fundamental.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FundamentalUnitCertificate {
    /// The squarefree `d`.
    pub radicand: BigInt,
    /// The rational part.
    pub a: BigInt,
    /// The `√d` part.
    pub b: BigInt,
    /// `a² − d b²`, which must be `±1`.
    pub norm: BigInt,
    /// Whether the *fundamental* claim was proved or only labelled.
    pub minimality: Minimality,
}

impl FundamentalUnitCertificate {
    /// Whether both halves — unit *and* fundamental — are certified.
    #[must_use]
    pub fn is_fully_certified(&self) -> bool {
        matches!(self.minimality, Minimality::ExhaustiveBelow { .. })
    }

    /// Re-derive the unit claim, and — when the certificate claims an
    /// exhaustive search — re-run that search independently.
    ///
    /// # Errors
    ///
    /// [`CertificateError::UnitRadicandNotRealQuadratic`],
    /// [`CertificateError::UnitNormMismatch`],
    /// [`CertificateError::NotAUnitNorm`],
    /// [`CertificateError::UnitNotPositive`],
    /// [`CertificateError::MinimalitySearchIncomplete`], or
    /// [`CertificateError::SmallerUnitExists`].
    pub fn verify(&self) -> Result<(), CertificateError> {
        // U1: d must be a positive non-square, or "the" fundamental unit is
        // not a thing.
        if !self.radicand.is_positive() {
            return Err(CertificateError::UnitRadicandNotRealQuadratic);
        }
        let root = self.radicand.sqrt();
        if &root * &root == self.radicand {
            return Err(CertificateError::UnitRadicandNotRealQuadratic);
        }
        // U2: the norm form, recomputed exactly.
        let recomputed = &self.a * &self.a - &self.radicand * &self.b * &self.b;
        if recomputed != self.norm {
            return Err(CertificateError::UnitNormMismatch);
        }
        // U3: only +-1 is a unit.
        if !self.norm.abs().is_one() {
            return Err(CertificateError::NotAUnitNorm);
        }
        // U4: "smallest" needs a positive representative.
        if !self.a.is_positive() || !self.b.is_positive() {
            return Err(CertificateError::UnitNotPositive);
        }
        // U5: the minimality search, re-run here, never inherited.
        if let Minimality::ExhaustiveBelow { searched } = &self.minimality {
            let bound =
                u64::try_from(&self.b).map_err(|_| CertificateError::MagnitudeOutOfRange)?;
            let required = bound - 1;
            if *searched != required {
                return Err(CertificateError::MinimalitySearchIncomplete {
                    claimed: *searched,
                    required,
                });
            }
            for candidate in 1..bound {
                let y = BigInt::from(candidate);
                let target = &self.radicand * &y * &y;
                for offset in [BigInt::one(), -BigInt::one()] {
                    let value = &target + &offset;
                    if value.is_negative() {
                        continue;
                    }
                    let x = value.sqrt();
                    if &x * &x == value && x.is_positive() {
                        return Err(CertificateError::SmallerUnitExists { witness: candidate });
                    }
                }
            }
        }
        Ok(())
    }
}

/// Convenience: the rational `value`, for building coefficient vectors in
/// callers and tests without importing `num_rational` directly.
#[must_use]
pub fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

/// Convenience: the integer `value` as a [`BigRational`].
#[must_use]
pub fn integer(value: i64) -> BigRational {
    rat_int(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn field(coeffs: &[i64]) -> NumberField {
        let poly: Vec<BigRational> = coeffs.iter().map(|&c| integer(c)).collect();
        NumberField::new(&poly).expect("field")
    }

    fn g(re: i64, im: i64) -> GaussianInt {
        GaussianInt::from_i64(re, im)
    }

    fn n(value: i64) -> BigInt {
        BigInt::from(value)
    }

    fn sorted_pair(cert: &TwoSquaresCertificate) -> (BigInt, BigInt) {
        match cert {
            TwoSquaresCertificate::Represented { a, b, .. } => {
                if a <= b {
                    (a.clone(), b.clone())
                } else {
                    (b.clone(), a.clone())
                }
            }
            TwoSquaresCertificate::Refuted { .. } => panic!("expected a representation"),
        }
    }

    // -----------------------------------------------------------------------
    // Field construction
    // -----------------------------------------------------------------------

    #[test]
    fn reducible_modulus_x_squared_minus_one_is_refused_with_its_own_reason() {
        let error = NumberField::new(&[integer(-1), integer(0), integer(1)]).unwrap_err();
        assert_eq!(error, CertificateError::ReducibleModulus { factors: 2 });
    }

    #[test]
    fn non_monic_modulus_is_refused_distinctly_from_a_reducible_one() {
        let error = NumberField::new(&[integer(-4), integer(0), integer(2)]).unwrap_err();
        assert_eq!(error, CertificateError::ModulusNotMonic);
    }

    #[test]
    fn constant_and_empty_moduli_are_refused_as_degenerate() {
        assert_eq!(
            NumberField::new(&[integer(3)]).unwrap_err(),
            CertificateError::ModulusDegenerate
        );
        assert_eq!(
            NumberField::new(&[]).unwrap_err(),
            CertificateError::ModulusDegenerate
        );
    }

    #[test]
    fn x_squared_minus_two_and_x_cubed_minus_two_are_accepted_as_fields() {
        assert_eq!(field(&[-2, 0, 1]).degree(), 2);
        assert_eq!(field(&[-2, 0, 0, 1]).degree(), 3);
        assert_eq!(field(&[1, 0, -10, 0, 1]).degree(), 4);
    }

    // -----------------------------------------------------------------------
    // Inverses
    // -----------------------------------------------------------------------

    #[test]
    fn q_sqrt2_inverse_of_one_plus_sqrt2_is_minus_one_plus_sqrt2() {
        let f = field(&[-2, 0, 1]);
        let element = f.element(&[integer(1), integer(1)]);
        let (inverse, certificate) = element.inverse().expect("invertible");
        assert_eq!(inverse.coeffs(), &[integer(-1), integer(1)]);
        assert_eq!(certificate.verify(), Ok(()));
        assert_eq!(element.mul(&inverse).expect("same field"), f.one());
    }

    #[test]
    fn q_cbrt2_inverse_of_one_plus_cbrt2_is_one_minus_a_plus_a_squared_over_three() {
        let f = field(&[-2, 0, 0, 1]);
        let element = f.element(&[integer(1), integer(1), integer(0)]);
        let (inverse, certificate) = element.inverse().expect("invertible");
        assert_eq!(
            inverse.coeffs(),
            &[rational(1, 3), rational(-1, 3), rational(1, 3)]
        );
        assert_eq!(certificate.verify(), Ok(()));
        assert_eq!(element.mul(&inverse).expect("same field"), f.one());
    }

    #[test]
    fn the_zero_element_has_no_inverse() {
        assert!(field(&[-2, 0, 1]).zero().inverse().is_none());
    }

    // -----------------------------------------------------------------------
    // Norm and trace
    // -----------------------------------------------------------------------

    #[test]
    fn norm_and_trace_of_one_plus_sqrt2_are_minus_one_and_two() {
        let f = field(&[-2, 0, 1]);
        let element = f.element(&[integer(1), integer(1)]);
        let certificate = element.norm_trace();
        assert_eq!(*certificate.norm(), integer(-1));
        assert_eq!(*certificate.trace(), integer(2));
        // chi(x) = x^2 - 2x - 1
        assert_eq!(
            certificate.char_poly,
            vec![integer(-1), integer(-2), integer(1)]
        );
        assert_eq!(certificate.verify(), Ok(()));
        assert_eq!(element.norm(), integer(-1));
        assert_eq!(element.trace(), integer(2));
    }

    #[test]
    fn norm_of_cbrt2_in_q_cbrt2_is_two() {
        let f = field(&[-2, 0, 0, 1]);
        let certificate = f.generator().norm_trace();
        assert_eq!(*certificate.norm(), integer(2));
        assert_eq!(*certificate.trace(), integer(0));
        assert_eq!(certificate.verify(), Ok(()));
    }

    // -----------------------------------------------------------------------
    // Minimal polynomial of an element
    // -----------------------------------------------------------------------

    #[test]
    fn minimal_polynomial_of_sqrt2_plus_sqrt3_is_x4_minus_10x2_plus_1() {
        let f = field(&[1, 0, -10, 0, 1]);
        let (poly, certificate) = f.generator().minimal_polynomial().expect("min poly");
        assert_eq!(
            poly,
            vec![integer(1), integer(0), integer(-10), integer(0), integer(1)]
        );
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn minimal_polynomial_of_sqrt2_inside_q_theta_is_x_squared_minus_two() {
        let f = field(&[1, 0, -10, 0, 1]);
        // sqrt(2) = (theta^3 - 9 theta) / 2 for theta = sqrt2 + sqrt3.
        let sqrt2 = f.element(&[integer(0), rational(-9, 2), integer(0), rational(1, 2)]);
        let (poly, certificate) = sqrt2.minimal_polynomial().expect("min poly");
        assert_eq!(poly, vec![integer(-2), integer(0), integer(1)]);
        assert_eq!(certificate.verify(), Ok(()));
        // The field norm and trace of a degree-2 element of a degree-4 field.
        let norm_trace = sqrt2.norm_trace();
        assert_eq!(*norm_trace.norm(), integer(4));
        assert_eq!(*norm_trace.trace(), integer(0));
        assert_eq!(norm_trace.verify(), Ok(()));
    }

    #[test]
    fn minimal_polynomial_of_a_rational_element_is_linear() {
        let f = field(&[-2, 0, 1]);
        let (poly, certificate) = f
            .rational(&integer(3))
            .minimal_polynomial()
            .expect("min poly");
        assert_eq!(poly, vec![integer(-3), integer(1)]);
        assert_eq!(certificate.verify(), Ok(()));
    }

    // -----------------------------------------------------------------------
    // Gaussian integers
    // -----------------------------------------------------------------------

    #[test]
    fn gaussian_divmod_leaves_a_remainder_of_smaller_norm() {
        let (quotient, remainder) = g(17, 4).divmod(&g(3, 2)).expect("nonzero divisor");
        assert_eq!(g(3, 2).mul(&quotient).add(&remainder), g(17, 4));
        assert!(remainder.norm() < g(3, 2).norm());
    }

    #[test]
    fn gaussian_gcd_of_five_and_two_plus_i_is_two_plus_i() {
        assert_eq!(g(5, 0).gcd(&g(2, 1)), g(2, 1));
    }

    #[test]
    fn canonical_associate_puts_every_unit_multiple_in_the_first_quadrant() {
        for value in [g(2, 1), g(-1, 2), g(-2, -1), g(1, -2)] {
            assert_eq!(value.canonical_associate(), g(2, 1));
        }
        assert_eq!(g(-3, 0).canonical_associate(), g(3, 0));
    }

    #[test]
    fn gaussian_factorization_of_five_splits_into_conjugate_primes() {
        let certificate = g(5, 0).factor().expect("factors");
        assert_eq!(certificate.factors, vec![g(1, 2), g(2, 1)]);
        assert_eq!(certificate.unit, g(0, -1));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn gaussian_factorization_of_two_is_ramified() {
        let certificate = g(2, 0).factor().expect("factors");
        assert_eq!(certificate.factors, vec![g(1, 1), g(1, 1)]);
        assert_eq!(certificate.unit, g(0, -1));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn gaussian_factorization_of_three_is_inert() {
        let certificate = g(3, 0).factor().expect("factors");
        assert_eq!(certificate.factors, vec![g(3, 0)]);
        assert_eq!(certificate.unit, g(1, 0));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn gaussian_factorization_of_one_plus_i_is_itself() {
        let certificate = g(1, 1).factor().expect("factors");
        assert_eq!(certificate.factors, vec![g(1, 1)]);
        assert_eq!(certificate.unit, g(1, 0));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn gaussian_factorization_of_minus_seven_tracks_the_unit() {
        let certificate = g(-7, 0).factor().expect("factors");
        assert_eq!(certificate.factors, vec![g(7, 0)]);
        assert_eq!(certificate.unit, g(-1, 0));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn gaussian_factorization_of_thirteen_sixty_five_and_thirty_verify_and_multiply_back() {
        for (value, expected_count) in [(g(13, 0), 2), (g(65, 0), 4), (g(30, 0), 5)] {
            let certificate = value.factor().expect("factors");
            assert_eq!(certificate.verify(), Ok(()), "value {value}");
            assert_eq!(certificate.factors.len(), expected_count, "value {value}");
            let mut product = certificate.unit.clone();
            for factor in &certificate.factors {
                product = product.mul(factor);
            }
            assert_eq!(product, value, "value {value}");
        }
    }

    #[test]
    fn gaussian_zero_declines_rather_than_returning_an_empty_factorization() {
        assert_eq!(g(0, 0).factor().unwrap_err(), DeclineReason::ZeroInput);
    }

    #[test]
    fn gaussian_primality_recognizes_the_three_kinds_and_rejects_units() {
        assert_eq!(g(1, 1).is_gaussian_prime(), Some(true));
        assert_eq!(g(2, 1).is_gaussian_prime(), Some(true));
        assert_eq!(g(3, 0).is_gaussian_prime(), Some(true));
        assert_eq!(g(0, -3).is_gaussian_prime(), Some(true));
        assert_eq!(g(5, 0).is_gaussian_prime(), Some(false));
        assert_eq!(g(1, 0).is_gaussian_prime(), Some(false));
        assert_eq!(g(0, 0).is_gaussian_prime(), Some(false));
    }

    // -----------------------------------------------------------------------
    // Two squares
    // -----------------------------------------------------------------------

    #[test]
    fn two_squares_of_five_is_one_plus_four() {
        let certificate = two_squares(&n(5)).expect("represented");
        assert_eq!(sorted_pair(&certificate), (n(1), n(2)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn two_squares_of_twenty_five_is_nine_plus_sixteen_and_the_checker_also_takes_zero_plus_25() {
        let certificate = two_squares(&n(25)).expect("represented");
        assert_eq!(sorted_pair(&certificate), (n(3), n(4)));
        assert_eq!(certificate.verify(), Ok(()));
        // The checker is independent of the producer: a different valid
        // representation of the same n also verifies.
        let other = TwoSquaresCertificate::Represented {
            n: n(25),
            a: n(0),
            b: n(5),
        };
        assert_eq!(other.verify(), Ok(()));
    }

    #[test]
    fn two_squares_of_forty_five_is_thirty_six_plus_nine() {
        let certificate = two_squares(&n(45)).expect("represented");
        assert_eq!(sorted_pair(&certificate), (n(3), n(6)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn two_squares_of_small_edge_cases() {
        for (value, expected) in [(0i64, (n(0), n(0))), (1, (n(0), n(1))), (2, (n(1), n(1)))] {
            let certificate = two_squares(&n(value)).expect("represented");
            assert_eq!(sorted_pair(&certificate), expected, "n = {value}");
            assert_eq!(certificate.verify(), Ok(()), "n = {value}");
        }
    }

    #[test]
    fn two_squares_of_twenty_one_is_refuted_by_three_to_the_first() {
        let certificate = two_squares(&n(21)).expect("refuted");
        match &certificate {
            TwoSquaresCertificate::Refuted {
                prime, exponent, ..
            } => {
                assert_eq!(*prime, 3);
                assert_eq!(*exponent, 1);
            }
            TwoSquaresCertificate::Represented { .. } => panic!("21 is not a sum of two squares"),
        }
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn two_squares_of_three_is_refuted() {
        let certificate = two_squares(&n(3)).expect("refuted");
        assert!(matches!(
            certificate,
            TwoSquaresCertificate::Refuted { prime: 3, .. }
        ));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn two_squares_of_mersenne_eighty_nine_declines_rather_than_lying() {
        let mersenne = (BigInt::one() << 89u32) - 1;
        assert_eq!(
            two_squares_outcome(&mersenne),
            TwoSquaresOutcome::Declined(DeclineReason::PrattCertificationTooExpensive {
                bound: PRATT_CERTIFY_BOUND
            })
        );
        assert!(two_squares(&mersenne).is_none());
    }

    #[test]
    fn two_squares_of_a_negative_declines() {
        assert_eq!(
            two_squares_outcome(&n(-5)),
            TwoSquaresOutcome::Declined(DeclineReason::NegativeInput)
        );
    }

    // -----------------------------------------------------------------------
    // Quadratic fields and units
    // -----------------------------------------------------------------------

    #[test]
    fn quadratic_field_refuses_a_non_squarefree_or_trivial_radicand() {
        for bad in [0i64, 1, -1, 4, 12, -8] {
            assert_eq!(
                QuadraticField::new(&n(bad)).unwrap_err(),
                CertificateError::RadicandNotAdmissible,
                "d = {bad}"
            );
        }
        assert!(QuadraticField::new(&n(2)).is_ok());
        assert!(QuadraticField::new(&n(-5)).is_ok());
    }

    #[test]
    fn fundamental_unit_for_d_two_is_one_plus_sqrt_two_and_is_fully_certified() {
        let quadratic = QuadraticField::new(&n(2)).expect("field");
        let unit = quadratic.fundamental_unit().expect("unit");
        assert_eq!(
            (unit.a.clone(), unit.b.clone(), unit.norm.clone()),
            (n(1), n(1), n(-1))
        );
        assert!(unit.is_fully_certified());
        assert_eq!(unit.verify(), Ok(()));
    }

    #[test]
    fn fundamental_unit_for_d_three_is_two_plus_sqrt_three_and_is_fully_certified() {
        let quadratic = QuadraticField::new(&n(3)).expect("field");
        let unit = quadratic.fundamental_unit().expect("unit");
        assert_eq!(
            (unit.a.clone(), unit.b.clone(), unit.norm.clone()),
            (n(2), n(1), n(1))
        );
        assert!(unit.is_fully_certified());
        assert_eq!(unit.verify(), Ok(()));
    }

    #[test]
    fn fundamental_unit_for_d_61_is_29718_plus_3805_sqrt_61_and_its_square_is_the_pell_unit() {
        let quadratic = QuadraticField::new(&n(61)).expect("field");
        let unit = quadratic.fundamental_unit().expect("unit");
        assert_eq!(unit.a, n(29_718));
        assert_eq!(unit.b, n(3_805));
        assert_eq!(unit.norm, n(-1));
        // b = 3805 is below the search bound, so minimality is proved here.
        assert!(unit.is_fully_certified());
        assert_eq!(unit.verify(), Ok(()));

        let pell = quadratic.pell_unit().expect("pell unit");
        assert_eq!(pell.a, BigInt::from(1_766_319_049_i64));
        assert_eq!(pell.b, BigInt::from(226_153_980_i64));
        assert_eq!(pell.norm, n(1));
        // b = 226153980 is past the search bound: the unit claim is checked,
        // the "fundamental" claim is labelled, never promoted.
        assert!(!pell.is_fully_certified());
        assert_eq!(pell.verify(), Ok(()));

        // Overflow control: the square of the fundamental unit is the Pell
        // unit, and a^2 here is about 3.1e18 -- past i64. Computed with
        // BigRational field arithmetic.
        let element = quadratic.element(
            &BigRational::from_integer(unit.a.clone()),
            &BigRational::from_integer(unit.b.clone()),
        );
        let square = element.mul(&element).expect("same field");
        assert_eq!(
            square.coeffs(),
            &[
                BigRational::from_integer(pell.a.clone()),
                BigRational::from_integer(pell.b.clone()),
            ]
        );
    }

    #[test]
    fn an_imaginary_quadratic_field_has_no_fundamental_unit_route() {
        let quadratic = QuadraticField::new(&n(-5)).expect("field");
        assert_eq!(
            quadratic.fundamental_unit().unwrap_err(),
            DeclineReason::NotRealQuadratic
        );
    }

    #[test]
    fn quadratic_norm_agrees_with_the_certified_field_norm() {
        let quadratic = QuadraticField::new(&n(2)).expect("field");
        let element = quadratic.element(&integer(1), &integer(1));
        let certificate = element.norm_trace();
        assert_eq!(certificate.verify(), Ok(()));
        assert_eq!(
            *certificate.norm(),
            BigRational::from_integer(quadratic.norm_form(&n(1), &n(1)))
        );
    }

    // -----------------------------------------------------------------------
    // Forged certificates: one distinct reason each
    // -----------------------------------------------------------------------

    fn sqrt2_field() -> NumberField {
        field(&[-2, 0, 1])
    }

    fn sqrt2_in_theta() -> Element {
        field(&[1, 0, -10, 0, 1]).element(&[
            integer(0),
            rational(-9, 2),
            integer(0),
            rational(1, 2),
        ])
    }

    #[test]
    fn forged_inverse_is_refused_naming_the_first_bad_coefficient() {
        let f = sqrt2_field();
        let (_, mut certificate) = f
            .element(&[integer(1), integer(1)])
            .inverse()
            .expect("invertible");
        certificate.inverse = vec![integer(1), integer(1)];
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::NotAnInverse { degree: 0 })
        );
    }

    #[test]
    fn forged_inverse_of_zero_is_refused_as_not_invertible() {
        let certificate = InverseCertificate {
            minpoly: sqrt2_field().minimal_polynomial().to_vec(),
            element: vec![integer(0), integer(0)],
            inverse: vec![integer(0), integer(0)],
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::ZeroIsNotInvertible)
        );
    }

    #[test]
    fn forged_norm_trace_with_a_wrong_multiplication_matrix_is_refused() {
        let mut certificate = sqrt2_field()
            .element(&[integer(1), integer(1)])
            .norm_trace();
        certificate.matrix[0][1] = integer(5);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::MultiplicationMatrixMismatch { row: 0, col: 1 })
        );
    }

    #[test]
    fn forged_norm_trace_with_a_non_monic_char_poly_is_refused() {
        let mut certificate = sqrt2_field()
            .element(&[integer(1), integer(1)])
            .norm_trace();
        certificate.char_poly = vec![integer(-1), integer(-2), integer(2)];
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::CharPolyNotMonic)
        );
    }

    #[test]
    fn forged_norm_trace_failing_cayley_hamilton_is_refused() {
        let mut certificate = sqrt2_field()
            .element(&[integer(1), integer(1)])
            .norm_trace();
        // Monic of the right degree, and internally consistent with the
        // recorded norm and trace, but not this matrix's characteristic
        // polynomial.
        certificate.char_poly = vec![integer(5), integer(-2), integer(1)];
        certificate.norm = integer(5);
        certificate.trace = integer(2);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::CayleyHamiltonFailed)
        );
    }

    #[test]
    fn forged_norm_trace_with_a_wrong_norm_is_refused() {
        let mut certificate = sqrt2_field()
            .element(&[integer(1), integer(1)])
            .norm_trace();
        certificate.norm = integer(7);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::NormNotCharPolyConstant)
        );
    }

    #[test]
    fn forged_norm_trace_with_a_wrong_trace_is_refused() {
        let mut certificate = sqrt2_field()
            .element(&[integer(1), integer(1)])
            .norm_trace();
        certificate.trace = integer(7);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::TraceNotCharPolySubleading)
        );
    }

    #[test]
    fn forged_norm_trace_whose_char_poly_constant_disagrees_with_the_determinant_is_refused() {
        // The multiplication matrix of sqrt2 inside a degree-4 field has
        // minimal polynomial x^2 - 2, strictly smaller than its characteristic
        // polynomial, so Cayley-Hamilton does NOT pin chi down: (x^2-2)(x^2+2)
        // annihilates it too. Only the independent determinant catches this.
        let mut certificate = sqrt2_in_theta().norm_trace();
        certificate.char_poly = vec![integer(-4), integer(0), integer(0), integer(0), integer(1)];
        certificate.norm = integer(-4);
        certificate.trace = integer(0);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::NormNotDeterminant)
        );
    }

    #[test]
    fn forged_norm_trace_whose_char_poly_subleading_disagrees_with_the_matrix_trace_is_refused() {
        // (x^2 - 2)(x^2 - x - 2) also annihilates the matrix and keeps the
        // determinant right, so only the independent matrix trace catches it.
        let mut certificate = sqrt2_in_theta().norm_trace();
        certificate.char_poly = vec![integer(4), integer(2), integer(-4), integer(-1), integer(1)];
        certificate.norm = integer(4);
        certificate.trace = integer(1);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::TraceNotMatrixTrace)
        );
    }

    #[test]
    fn forged_element_min_poly_that_is_not_monic_is_refused() {
        let f = sqrt2_field();
        let certificate = ElementMinPolyCertificate {
            minpoly: f.minimal_polynomial().to_vec(),
            element: vec![integer(0), integer(1)],
            poly: vec![integer(-4), integer(0), integer(2)],
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::MinimalPolynomialNotMonic)
        );
    }

    #[test]
    fn forged_element_min_poly_the_element_does_not_satisfy_is_refused() {
        let f = sqrt2_field();
        let certificate = ElementMinPolyCertificate {
            minpoly: f.minimal_polynomial().to_vec(),
            element: vec![integer(0), integer(1)],
            poly: vec![integer(-3), integer(0), integer(1)],
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::MinimalPolynomialNotSatisfied)
        );
    }

    #[test]
    fn forged_element_min_poly_that_is_reducible_is_refused() {
        let f = sqrt2_field();
        // (x^2 - 2)^2 is monic and sqrt2 satisfies it, but it is not minimal.
        let certificate = ElementMinPolyCertificate {
            minpoly: f.minimal_polynomial().to_vec(),
            element: vec![integer(0), integer(1)],
            poly: vec![integer(4), integer(0), integer(-4), integer(0), integer(1)],
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::MinimalPolynomialReducible)
        );
    }

    #[test]
    fn forged_gaussian_factorization_of_zero_is_refused() {
        let certificate = GaussianFactorizationCertificate {
            value: g(0, 0),
            unit: g(1, 0),
            factors: Vec::new(),
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::ZeroHasNoFactorization)
        );
    }

    #[test]
    fn forged_gaussian_unit_that_is_not_a_unit_is_refused() {
        let mut certificate = g(5, 0).factor().expect("factors");
        certificate.unit = g(1, 1);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::NotAGaussianUnit)
        );
    }

    #[test]
    fn forged_gaussian_product_that_does_not_multiply_back_is_refused() {
        let mut certificate = g(5, 0).factor().expect("factors");
        // A genuine unit, but the wrong one.
        certificate.unit = g(0, 1);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::GaussianProductMismatch)
        );
    }

    #[test]
    fn forged_gaussian_factor_that_is_not_a_gaussian_prime_is_refused() {
        let certificate = GaussianFactorizationCertificate {
            value: g(5, 0),
            unit: g(1, 0),
            factors: vec![g(5, 0)],
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::NotAGaussianPrime { index: 0 })
        );
    }

    #[test]
    fn forged_two_squares_with_a_wrong_sum_is_refused() {
        let certificate = TwoSquaresCertificate::Represented {
            n: n(5),
            a: n(1),
            b: n(1),
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::SumOfSquaresMismatch)
        );
    }

    #[test]
    fn forged_two_squares_for_a_negative_n_is_refused() {
        let certificate = TwoSquaresCertificate::Represented {
            n: n(-5),
            a: n(1),
            b: n(2),
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::NegativeSumOfSquares)
        );
    }

    #[test]
    fn forged_two_squares_refutation_with_a_broken_factorization_is_refused() {
        let TwoSquaresCertificate::Refuted {
            n: value,
            mut factorization,
            prime,
            exponent,
        } = two_squares(&n(21)).expect("refuted")
        else {
            panic!("21 is refuted");
        };
        factorization.factors[0].1 = 4;
        let forged = TwoSquaresCertificate::Refuted {
            n: value,
            factorization,
            prime,
            exponent,
        };
        assert_eq!(
            forged.verify(),
            Err(CertificateError::FactorizationCertificateInvalid)
        );
    }

    #[test]
    fn forged_two_squares_refutation_naming_an_absent_exponent_is_refused() {
        let TwoSquaresCertificate::Refuted {
            n: value,
            factorization,
            prime,
            ..
        } = two_squares(&n(21)).expect("refuted")
        else {
            panic!("21 is refuted");
        };
        let forged = TwoSquaresCertificate::Refuted {
            n: value,
            factorization,
            prime,
            exponent: 3,
        };
        assert_eq!(
            forged.verify(),
            Err(CertificateError::RefutationExponentNotInFactorization)
        );
    }

    #[test]
    fn forged_two_squares_refutation_naming_a_prime_that_is_one_mod_four_is_refused() {
        // 45 = 3^2 * 5 IS a sum of two squares; a refutation naming 5^1 is
        // arithmetically truthful about the factorization and still no proof.
        let factorization = certify_factorization(45).expect("pratt");
        let forged = TwoSquaresCertificate::Refuted {
            n: n(45),
            factorization,
            prime: 5,
            exponent: 1,
        };
        assert_eq!(
            forged.verify(),
            Err(CertificateError::RefutationPrimeNotThreeModFour)
        );
    }

    #[test]
    fn forged_two_squares_refutation_naming_an_even_exponent_is_refused() {
        let factorization = certify_factorization(45).expect("pratt");
        let forged = TwoSquaresCertificate::Refuted {
            n: n(45),
            factorization,
            prime: 3,
            exponent: 2,
        };
        assert_eq!(
            forged.verify(),
            Err(CertificateError::RefutationExponentEven)
        );
    }

    #[test]
    fn forged_unit_over_a_square_radicand_is_refused() {
        let certificate = FundamentalUnitCertificate {
            radicand: n(4),
            a: n(3),
            b: n(1),
            norm: n(5),
            minimality: Minimality::ExhaustiveBelow { searched: 0 },
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::UnitRadicandNotRealQuadratic)
        );
    }

    #[test]
    fn forged_unit_whose_norm_form_disagrees_is_refused() {
        let certificate = FundamentalUnitCertificate {
            radicand: n(2),
            a: n(3),
            b: n(2),
            norm: n(99),
            minimality: Minimality::ExhaustiveBelow { searched: 1 },
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::UnitNormMismatch)
        );
    }

    #[test]
    fn forged_unit_whose_norm_is_not_plus_or_minus_one_is_refused() {
        let certificate = FundamentalUnitCertificate {
            radicand: n(2),
            a: n(2),
            b: n(1),
            norm: n(2),
            minimality: Minimality::ExhaustiveBelow { searched: 0 },
        };
        assert_eq!(certificate.verify(), Err(CertificateError::NotAUnitNorm));
    }

    #[test]
    fn forged_unit_with_a_non_positive_component_is_refused() {
        let certificate = FundamentalUnitCertificate {
            radicand: n(2),
            a: n(1),
            b: n(0),
            norm: n(1),
            minimality: Minimality::ExhaustiveBelow { searched: 0 },
        };
        assert_eq!(certificate.verify(), Err(CertificateError::UnitNotPositive));
    }

    #[test]
    fn forged_unit_claiming_an_incomplete_search_is_refused() {
        let certificate = FundamentalUnitCertificate {
            radicand: n(2),
            a: n(3),
            b: n(2),
            norm: n(1),
            minimality: Minimality::ExhaustiveBelow { searched: 5 },
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::MinimalitySearchIncomplete {
                claimed: 5,
                required: 1
            })
        );
    }

    #[test]
    fn forged_unit_with_a_smaller_unit_below_it_is_refused() {
        // 3 + 2*sqrt2 IS a unit, but 1 + sqrt2 is smaller, and the checker
        // re-runs the search rather than inheriting the producer's word.
        let certificate = FundamentalUnitCertificate {
            radicand: n(2),
            a: n(3),
            b: n(2),
            norm: n(1),
            minimality: Minimality::ExhaustiveBelow { searched: 1 },
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::SmallerUnitExists { witness: 1 })
        );
    }
}
