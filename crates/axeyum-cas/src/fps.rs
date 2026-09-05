//! Formal power series and generating functions as a first-class object.
//!
//! A [`FormalPowerSeries`] is a truncated element of `ℚ[[x]]`: a dense,
//! least-significant-first vector of exact [`BigRational`] coefficients together
//! with a truncation `order`, understood modulo `x^(order+1)`. Unlike the
//! private `Series` helper behind [`crate::series`] — whose coefficients are the
//! machine-width `axeyum_ir::Rational` and which exists only to expand a
//! [`CasExpr`] — this module is arbitrary-precision throughout, so Catalan,
//! factorial and Bernoulli-sized coefficients do not overflow.
//!
//! # What carries a certificate
//!
//! The operations that *invert* something — series inversion, compositional
//! inversion (reversion), and the expansion of a rational function — return a
//! [`TruncationIdentity`] whose [`verify`](TruncationIdentity::verify)
//! re-derives the defining identity modulo `x^(order+1)` by multiplying or
//! composing back. Recurrence work returns a [`RecurrenceCertificate`] whose
//! `verify` re-checks the recurrence at **every** supplied term. Both checkers
//! are independent of the producer: they never consult how the answer was
//! found, only whether the stated identity holds.
//!
//! The ring operations (`add`, `sub`, `neg`, `scale`, `mul`, `derivative`,
//! `integral`, `compose`, the shifts) are documented `uncertified`: there is no
//! check of a Cauchy product cheaper than recomputing the Cauchy product, so a
//! "certificate" for them would be the producer wearing a hat.
//!
//! # Out of scope, deliberately
//!
//! - **Coefficient asymptotics.** Singularity analysis needs complex-analytic
//!   machinery this crate does not have.
//! - **Radius of convergence.** Even in the rational case the honest bound is
//!   `1/max|root|` over the **complex** roots of the denominator; the existing
//!   Sturm / real-root machinery certifies real roots only, so no exact
//!   certificate is available and nothing is shipped rather than shipping a
//!   bound that is wrong on `1/(1+x²)`.
//! - **P-recursive (holonomic) guessing.** [`guess_linear_recurrence`] fits
//!   *constant* coefficients only; polynomial-coefficient guessing is a
//!   different linear system and a different certificate.

use core::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::CasExpr;

/// Why a certificate was refused. Each variant names a distinct, independently
/// reachable guard so a refusal says *what* failed, not merely that it did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertificateError {
    /// A series in the certificate is truncated at a different order than the
    /// order the certificate claims to establish.
    OrderMismatch {
        /// The order the certificate asserts.
        expected: usize,
        /// The order actually carried by the series.
        found: usize,
    },
    /// The stated identity fails at this degree.
    IdentityFailed {
        /// The lowest degree at which the two sides disagree.
        degree: usize,
    },
    /// A constant (or linear) term required to be zero is nonzero, or one
    /// required to be nonzero is zero.
    DegenerateTerm {
        /// The degree of the offending coefficient.
        degree: usize,
    },
    /// The certificate's polynomial data reaches past the truncation order, so
    /// part of it is never examined by the check.
    DataPastTruncation {
        /// Number of coefficients supplied.
        supplied: usize,
        /// The truncation order the certificate claims.
        order: usize,
    },
    /// A recurrence certificate carrying no equation to check: with `order`
    /// coefficients and `terms` terms there are `terms - order` equations, and
    /// a checker with zero equations cannot fail.
    VacuousRecurrence {
        /// The recurrence order.
        order: usize,
        /// The number of terms supplied.
        terms: usize,
    },
    /// The recurrence does not reproduce the term at this index.
    RecurrenceFailed {
        /// Index of the first term the recurrence gets wrong.
        index: usize,
    },
    /// The declared fitted-term count disagrees with the terms actually carried.
    TermCountMismatch {
        /// The count the certificate declares.
        declared: usize,
        /// The number of terms actually present.
        found: usize,
    },
    /// The inner certificate describes a different object than the one it is
    /// attached to.
    CertificateMismatch,
    /// A denominator polynomial was empty.
    EmptyDenominator,
}

impl fmt::Display for CertificateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CertificateError::OrderMismatch { expected, found } => {
                write!(
                    f,
                    "truncation order mismatch: claimed {expected}, got {found}"
                )
            }
            CertificateError::IdentityFailed { degree } => {
                write!(f, "identity fails at degree {degree}")
            }
            CertificateError::DegenerateTerm { degree } => {
                write!(
                    f,
                    "coefficient of degree {degree} violates the side condition"
                )
            }
            CertificateError::DataPastTruncation { supplied, order } => write!(
                f,
                "{supplied} coefficients supplied but only degrees 0..={order} are checked"
            ),
            CertificateError::VacuousRecurrence { order, terms } => write!(
                f,
                "vacuous recurrence certificate: order {order} with only {terms} terms"
            ),
            CertificateError::RecurrenceFailed { index } => {
                write!(f, "recurrence fails at term {index}")
            }
            CertificateError::TermCountMismatch { declared, found } => {
                write!(f, "declared {declared} fitted terms but carries {found}")
            }
            CertificateError::CertificateMismatch => {
                write!(f, "inner certificate describes a different object")
            }
            CertificateError::EmptyDenominator => write!(f, "empty denominator polynomial"),
        }
    }
}

impl core::error::Error for CertificateError {}

fn zero() -> BigRational {
    BigRational::zero()
}

fn from_usize(value: usize) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

/// Truncated product of two coefficient vectors, keeping degrees `0..=order`.
fn truncated_mul(left: &[BigRational], right: &[BigRational], order: usize) -> Vec<BigRational> {
    let mut result = vec![zero(); order + 1];
    for (i, a) in left.iter().enumerate() {
        if i > order || a.is_zero() {
            continue;
        }
        for (j, b) in right.iter().enumerate() {
            if i + j > order {
                break;
            }
            result[i + j] += a * b;
        }
    }
    result
}

/// A truncated formal power series over ℚ.
///
/// The coefficient vector always has length `order + 1`; index `i` holds the
/// exact coefficient of `x^i`. Nothing is asserted about degrees above `order`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormalPowerSeries {
    coeffs: Vec<BigRational>,
    order: usize,
}

impl FormalPowerSeries {
    /// Adopt a coefficient vector, truncating or zero-padding it to `order`.
    ///
    /// `uncertified` — a constructor asserts nothing beyond the coefficients it
    /// was handed.
    pub fn from_coefficients(coeffs: &[BigRational], order: usize) -> FormalPowerSeries {
        let mut coeffs = coeffs.to_vec();
        coeffs.truncate(order + 1);
        coeffs.resize(order + 1, zero());
        FormalPowerSeries { coeffs, order }
    }

    /// The zero series of the given truncation order. `uncertified` (trivial).
    pub fn zero(order: usize) -> FormalPowerSeries {
        FormalPowerSeries {
            coeffs: vec![zero(); order + 1],
            order,
        }
    }

    /// The constant series `1`. `uncertified` (trivial).
    pub fn one(order: usize) -> FormalPowerSeries {
        Self::constant(&BigRational::one(), order)
    }

    /// The constant series `value`. `uncertified` (trivial).
    pub fn constant(value: &BigRational, order: usize) -> FormalPowerSeries {
        let mut series = Self::zero(order);
        series.coeffs[0] = value.clone();
        series
    }

    /// The series `x`, to the given truncation order. `uncertified` (trivial).
    pub fn identity(order: usize) -> FormalPowerSeries {
        let mut series = Self::zero(order);
        if order >= 1 {
            series.coeffs[1] = BigRational::one();
        }
        series
    }

    /// The truncation order: coefficients `0..=order` are known.
    pub fn order(&self) -> usize {
        self.order
    }

    /// All known coefficients, least-significant first.
    pub fn coefficients(&self) -> &[BigRational] {
        &self.coeffs
    }

    /// The coefficient of `x^n`, or `None` when `n` is past the truncation —
    /// a truncated series does not know that coefficient, and returning zero
    /// there would be a false statement rather than a missing one.
    pub fn coefficient(&self, n: usize) -> Option<&BigRational> {
        self.coeffs.get(n)
    }

    /// Re-truncate to a lower (or equal) order. `uncertified` (trivial).
    pub fn truncated(&self, order: usize) -> FormalPowerSeries {
        Self::from_coefficients(&self.coeffs, order.min(self.order))
    }

    /// Coefficient-wise sum, truncated to the lower of the two orders.
    ///
    /// `uncertified`: re-deriving a sum is the same addition.
    pub fn add(&self, other: &FormalPowerSeries) -> FormalPowerSeries {
        let order = self.order.min(other.order);
        let coeffs = (0..=order)
            .map(|i| &self.coeffs[i] + &other.coeffs[i])
            .collect();
        FormalPowerSeries { coeffs, order }
    }

    /// Coefficient-wise difference. `uncertified`, as [`add`](Self::add).
    pub fn sub(&self, other: &FormalPowerSeries) -> FormalPowerSeries {
        let order = self.order.min(other.order);
        let coeffs = (0..=order)
            .map(|i| &self.coeffs[i] - &other.coeffs[i])
            .collect();
        FormalPowerSeries { coeffs, order }
    }

    /// Negation. `uncertified`, as [`add`](Self::add).
    pub fn neg(&self) -> FormalPowerSeries {
        FormalPowerSeries {
            coeffs: self.coeffs.iter().map(|c| -c).collect(),
            order: self.order,
        }
    }

    /// Scalar multiple. `uncertified`, as [`add`](Self::add).
    pub fn scale(&self, factor: &BigRational) -> FormalPowerSeries {
        FormalPowerSeries {
            coeffs: self.coeffs.iter().map(|c| c * factor).collect(),
            order: self.order,
        }
    }

    /// Cauchy product, truncated to the lower of the two orders.
    ///
    /// `uncertified`: the only independent check of a Cauchy product is the
    /// same Cauchy product.
    pub fn mul(&self, other: &FormalPowerSeries) -> FormalPowerSeries {
        let order = self.order.min(other.order);
        FormalPowerSeries {
            coeffs: truncated_mul(&self.coeffs, &other.coeffs, order),
            order,
        }
    }

    /// Multiply by `x^k`, keeping the same truncation order (so the top `k`
    /// coefficients fall off the end). `uncertified`, as [`add`](Self::add).
    pub fn mul_by_x_pow(&self, k: usize) -> FormalPowerSeries {
        let mut coeffs = vec![zero(); self.order + 1];
        for (i, c) in self.coeffs.iter().enumerate() {
            if i + k <= self.order {
                coeffs[i + k] = c.clone();
            }
        }
        FormalPowerSeries {
            coeffs,
            order: self.order,
        }
    }

    /// Divide by `x^k`, lowering the truncation order to `order - k`. `None`
    /// unless the first `k` coefficients all vanish (otherwise the quotient is
    /// not a power series) or `k > order`.
    ///
    /// `uncertified`, as [`add`](Self::add) — but note the divisibility side
    /// condition is *checked*, not assumed.
    pub fn div_by_x_pow(&self, k: usize) -> Option<FormalPowerSeries> {
        if k > self.order {
            return None;
        }
        if self.coeffs.iter().take(k).any(|c| !c.is_zero()) {
            return None;
        }
        Some(FormalPowerSeries {
            coeffs: self.coeffs[k..].to_vec(),
            order: self.order - k,
        })
    }

    /// Formal derivative; the truncation order drops by one (a series known to
    /// `x^n` determines its derivative only to `x^(n-1)`).
    ///
    /// `uncertified`, as [`add`](Self::add).
    pub fn derivative(&self) -> FormalPowerSeries {
        let order = self.order.saturating_sub(1);
        let coeffs = (0..=order)
            .map(|i| {
                self.coeffs
                    .get(i + 1)
                    .map_or_else(zero, |c| c * from_usize(i + 1))
            })
            .collect();
        FormalPowerSeries { coeffs, order }
    }

    /// Formal integral with zero constant of integration; the truncation order
    /// rises by one. `uncertified`, as [`add`](Self::add).
    pub fn integral(&self) -> FormalPowerSeries {
        let order = self.order + 1;
        let mut coeffs = vec![zero(); order + 1];
        for (i, c) in self.coeffs.iter().enumerate() {
            coeffs[i + 1] = c / from_usize(i + 1);
        }
        FormalPowerSeries { coeffs, order }
    }

    /// The multiplicative inverse `1/f`, which exists iff `f(0) ≠ 0`.
    ///
    /// Returns the inverse together with a [`TruncationIdentity::Inverse`]
    /// certificate whose `verify` recomputes `f · f⁻¹` and checks it is `1`
    /// modulo `x^(order+1)`. `None` when `f(0) = 0`.
    pub fn inverse(&self) -> Option<(FormalPowerSeries, TruncationIdentity)> {
        let lead = self.coeffs.first()?;
        if lead.is_zero() {
            return None;
        }
        let mut inverse = vec![zero(); self.order + 1];
        inverse[0] = BigRational::one() / lead;
        for n in 1..=self.order {
            let mut acc = zero();
            for k in 1..=n {
                acc += &self.coeffs[k] * &inverse[n - k];
            }
            inverse[n] = -acc / lead;
        }
        let inverse = FormalPowerSeries {
            coeffs: inverse,
            order: self.order,
        };
        let certificate = TruncationIdentity::Inverse {
            series: self.clone(),
            inverse: inverse.clone(),
            order: self.order,
        };
        Some((inverse, certificate))
    }

    /// Composition `self ∘ inner`, requiring `inner(0) = 0` so the composite is
    /// again a formal power series. The result is truncated to the lower of the
    /// two orders.
    ///
    /// `uncertified`: composition is a Horner evaluation and re-deriving it is
    /// the same evaluation. Composition *does* appear inside the reversion
    /// certificate, where it checks an independent claim.
    pub fn compose(&self, inner: &FormalPowerSeries) -> Option<FormalPowerSeries> {
        if !inner.coeffs.first()?.is_zero() {
            return None;
        }
        let order = self.order.min(inner.order);
        let inner_coeffs = &inner.coeffs[..=order];
        let mut acc = vec![zero(); order + 1];
        for coeff in self.coeffs[..=order].iter().rev() {
            acc = truncated_mul(&acc, inner_coeffs, order);
            acc[0] += coeff;
        }
        Some(FormalPowerSeries { coeffs: acc, order })
    }

    /// The compositional inverse (**reversion**) `g` with `self(g(x)) = x`,
    /// which exists iff `self(0) = 0` and `self'(0) ≠ 0`.
    ///
    /// Returns `g` with a [`TruncationIdentity::Reversion`] certificate whose
    /// `verify` composes `self ∘ g` back and checks it is `x` modulo
    /// `x^(order+1)`.
    pub fn reversion(&self) -> Option<(FormalPowerSeries, TruncationIdentity)> {
        if !self.coeffs.first()?.is_zero() {
            return None;
        }
        let linear = self.coeffs.get(1)?.clone();
        if linear.is_zero() {
            return None;
        }
        let mut reverted = vec![zero(); self.order + 1];
        if self.order >= 1 {
            reverted[1] = BigRational::one() / &linear;
        }
        for n in 2..=self.order {
            let partial = FormalPowerSeries {
                coeffs: reverted[..=n].to_vec(),
                order: n,
            };
            let composed = self.truncated(n).compose(&partial)?;
            reverted[n] = -composed.coeffs[n].clone() / &linear;
        }
        let reverted = FormalPowerSeries {
            coeffs: reverted,
            order: self.order,
        };
        let certificate = TruncationIdentity::Reversion {
            series: self.clone(),
            reversion: reverted.clone(),
            order: self.order,
        };
        Some((reverted, certificate))
    }

    /// The exact power-series expansion of the rational function `p/q` with
    /// `q(0) ≠ 0`, to the given truncation order.
    ///
    /// Returns the expansion with a
    /// [`TruncationIdentity::RationalExpansion`] certificate whose `verify`
    /// multiplies `q · expansion` back and checks it equals `p` modulo
    /// `x^(order+1)`. `None` when `q` is empty, `q(0) = 0`, or either
    /// polynomial reaches past the truncation order (in which case the
    /// certificate could not examine all of its own data).
    pub fn from_rational_function(
        numerator: &[BigRational],
        denominator: &[BigRational],
        order: usize,
    ) -> Option<(FormalPowerSeries, TruncationIdentity)> {
        if denominator.first()?.is_zero() {
            return None;
        }
        if numerator.len() > order + 1 || denominator.len() > order + 1 {
            return None;
        }
        let denominator_series = Self::from_coefficients(denominator, order);
        let (inverse, _) = denominator_series.inverse()?;
        let expansion = Self::from_coefficients(numerator, order).mul(&inverse);
        let certificate = TruncationIdentity::RationalExpansion {
            numerator: numerator.to_vec(),
            denominator: denominator.to_vec(),
            expansion: expansion.clone(),
            order,
        };
        Some((expansion, certificate))
    }

    /// Unroll a constant-coefficient linear recurrence from `initial_terms` out
    /// to `order`, returning the generating series together with a
    /// [`RecurrenceCertificate`] over every term produced.
    ///
    /// `None` when the recurrence is malformed, when fewer initial terms are
    /// supplied than its order, or when `order` is too small for the
    /// recurrence to fire even once (a certificate with no equation to check
    /// is refused at the source, not only at `verify`).
    pub fn from_recurrence(
        recurrence: &RecurrenceCertificate,
        initial_terms: &[BigRational],
        order: usize,
    ) -> Option<(FormalPowerSeries, RecurrenceCertificate)> {
        let degree = recurrence.order;
        if recurrence.coefficients.len() != degree {
            return None;
        }
        if initial_terms.len() < degree || order + 1 <= degree {
            return None;
        }
        let mut terms: Vec<BigRational> = initial_terms
            .iter()
            .take((order + 1).min(initial_terms.len()))
            .cloned()
            .collect();
        while terms.len() <= order {
            let n = terms.len();
            let mut next = zero();
            for (k, coeff) in recurrence.coefficients.iter().enumerate() {
                next += coeff * &terms[n - (k + 1)];
            }
            terms.push(next);
        }
        let series = Self::from_coefficients(&terms, order);
        let certificate = RecurrenceCertificate::new(recurrence.coefficients.clone(), terms);
        Some((series, certificate))
    }

    /// The Maclaurin coefficients of a [`CasExpr`] as a formal power series,
    /// by reusing the crate's existing expansion engine
    /// (`crate::series_coefficients`, i.e. [`crate::series`] plus
    /// [`crate::normalize`]) and widening its machine-width rationals to
    /// [`BigRational`].
    ///
    /// `uncertified`, twice over: the underlying expansion is documented as a
    /// compute operation with no certificate, and its coefficients are computed
    /// in checked `i128` rationals so an expansion that overflows there
    /// declines to `None` rather than reaching this function.
    pub fn from_cas_expr(expr: &CasExpr, var: &str, order: usize) -> Option<FormalPowerSeries> {
        let coeffs = crate::series_coefficients(expr, var, order)?;
        let widened: Vec<BigRational> = coeffs
            .iter()
            .map(|c| BigRational::new(BigInt::from(c.numerator()), BigInt::from(c.denominator())))
            .collect();
        Some(Self::from_coefficients(&widened, order))
    }
}

/// A checkable identity between truncated series, verified modulo
/// `x^(order+1)` by recomputing the product or composition it asserts.
///
/// Every variant's `verify` re-derives its claim from the carried data alone;
/// none of them consults how the answer was produced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TruncationIdentity {
    /// `series · inverse ≡ 1  (mod x^(order+1))`.
    Inverse {
        /// The series being inverted.
        series: FormalPowerSeries,
        /// The claimed inverse.
        inverse: FormalPowerSeries,
        /// The truncation order the identity is asserted at.
        order: usize,
    },
    /// `series ∘ reversion ≡ x  (mod x^(order+1))`.
    Reversion {
        /// The series being reverted.
        series: FormalPowerSeries,
        /// The claimed compositional inverse.
        reversion: FormalPowerSeries,
        /// The truncation order the identity is asserted at.
        order: usize,
    },
    /// `denominator · expansion ≡ numerator  (mod x^(order+1))`.
    RationalExpansion {
        /// Numerator polynomial, least-significant first.
        numerator: Vec<BigRational>,
        /// Denominator polynomial, least-significant first; `q(0) ≠ 0`.
        denominator: Vec<BigRational>,
        /// The claimed expansion.
        expansion: FormalPowerSeries,
        /// The truncation order the identity is asserted at.
        order: usize,
    },
}

impl TruncationIdentity {
    /// The truncation order this identity is asserted at.
    pub fn order(&self) -> usize {
        match self {
            TruncationIdentity::Inverse { order, .. }
            | TruncationIdentity::Reversion { order, .. }
            | TruncationIdentity::RationalExpansion { order, .. } => *order,
        }
    }

    /// Re-derive the asserted identity and accept or refuse it.
    ///
    /// # Errors
    ///
    /// Returns the specific [`CertificateError`] that fired: a truncation-order
    /// mismatch, a violated side condition on a low-order coefficient, data
    /// reaching past the truncation, or the lowest degree at which the identity
    /// fails.
    pub fn verify(&self) -> Result<(), CertificateError> {
        match self {
            TruncationIdentity::Inverse {
                series,
                inverse,
                order,
            } => {
                check_order(series, *order)?;
                check_order(inverse, *order)?;
                if series.coefficients()[0].is_zero() {
                    return Err(CertificateError::DegenerateTerm { degree: 0 });
                }
                let product = truncated_mul(series.coefficients(), inverse.coefficients(), *order);
                check_equals_monomial(&product, 0, *order)
            }
            TruncationIdentity::Reversion {
                series,
                reversion,
                order,
            } => {
                check_order(series, *order)?;
                check_order(reversion, *order)?;
                if !series.coefficients()[0].is_zero() {
                    return Err(CertificateError::DegenerateTerm { degree: 0 });
                }
                if !reversion.coefficients()[0].is_zero() {
                    return Err(CertificateError::DegenerateTerm { degree: 0 });
                }
                if *order >= 1 && series.coefficients()[1].is_zero() {
                    return Err(CertificateError::DegenerateTerm { degree: 1 });
                }
                let composed = series
                    .compose(reversion)
                    .ok_or(CertificateError::DegenerateTerm { degree: 0 })?;
                check_equals_monomial(composed.coefficients(), 1, *order)
            }
            TruncationIdentity::RationalExpansion {
                numerator,
                denominator,
                expansion,
                order,
            } => {
                if denominator.is_empty() {
                    return Err(CertificateError::EmptyDenominator);
                }
                if denominator[0].is_zero() {
                    return Err(CertificateError::DegenerateTerm { degree: 0 });
                }
                if numerator.len() > order + 1 {
                    return Err(CertificateError::DataPastTruncation {
                        supplied: numerator.len(),
                        order: *order,
                    });
                }
                if denominator.len() > order + 1 {
                    return Err(CertificateError::DataPastTruncation {
                        supplied: denominator.len(),
                        order: *order,
                    });
                }
                check_order(expansion, *order)?;
                let product = truncated_mul(denominator, expansion.coefficients(), *order);
                for degree in 0..=*order {
                    let expected = numerator.get(degree).cloned().unwrap_or_else(zero);
                    if product[degree] != expected {
                        return Err(CertificateError::IdentityFailed { degree });
                    }
                }
                Ok(())
            }
        }
    }
}

fn check_order(series: &FormalPowerSeries, order: usize) -> Result<(), CertificateError> {
    if series.order() == order {
        Ok(())
    } else {
        Err(CertificateError::OrderMismatch {
            expected: order,
            found: series.order(),
        })
    }
}

/// Check `coeffs ≡ x^power` over degrees `0..=order`.
fn check_equals_monomial(
    coeffs: &[BigRational],
    power: usize,
    order: usize,
) -> Result<(), CertificateError> {
    for degree in 0..=order {
        let expected = if degree == power {
            BigRational::one()
        } else {
            zero()
        };
        let found = coeffs.get(degree).cloned().unwrap_or_else(zero);
        if found != expected {
            return Err(CertificateError::IdentityFailed { degree });
        }
    }
    Ok(())
}

/// A constant-coefficient linear recurrence together with the terms it is
/// asserted to reproduce.
///
/// The claim is `a_n = Σ_{k=1..=order} c_k · a_{n−k}` for every
/// `n` in `order..terms.len()`, and [`verify`](RecurrenceCertificate::verify)
/// re-checks that equation at **every** such term. The fields are public
/// because a certificate is data, not a promise: `verify` is the judge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecurrenceCertificate {
    /// `c_1, …, c_order`: `coefficients[k]` multiplies `a_{n−(k+1)}`.
    pub coefficients: Vec<BigRational>,
    /// The recurrence order (must equal `coefficients.len()`).
    pub order: usize,
    /// The number of terms the recurrence was fitted on (must equal
    /// `terms.len()`).
    pub terms_fitted: usize,
    /// The terms the recurrence is asserted to reproduce.
    pub terms: Vec<BigRational>,
}

impl RecurrenceCertificate {
    /// Build a certificate from a coefficient vector and the terms it claims to
    /// reproduce. Nothing is checked here — call
    /// [`verify`](RecurrenceCertificate::verify).
    pub fn new(coefficients: Vec<BigRational>, terms: Vec<BigRational>) -> RecurrenceCertificate {
        RecurrenceCertificate {
            order: coefficients.len(),
            terms_fitted: terms.len(),
            coefficients,
            terms,
        }
    }

    /// Re-check the recurrence at every supplied term.
    ///
    /// # Errors
    ///
    /// Refuses a certificate whose declared order disagrees with its
    /// coefficient vector, whose declared fitted-term count disagrees with the
    /// terms it carries, that carries too few terms for a single equation to be
    /// checked (which would make the checker unable to fail), or that fails the
    /// recurrence at some index.
    pub fn verify(&self) -> Result<(), CertificateError> {
        if self.coefficients.len() != self.order {
            return Err(CertificateError::OrderMismatch {
                expected: self.order,
                found: self.coefficients.len(),
            });
        }
        if self.terms.len() != self.terms_fitted {
            return Err(CertificateError::TermCountMismatch {
                declared: self.terms_fitted,
                found: self.terms.len(),
            });
        }
        if self.terms.len() <= self.order {
            return Err(CertificateError::VacuousRecurrence {
                order: self.order,
                terms: self.terms.len(),
            });
        }
        for index in self.order..self.terms.len() {
            let mut predicted = zero();
            for (k, coeff) in self.coefficients.iter().enumerate() {
                predicted += coeff * &self.terms[index - (k + 1)];
            }
            if predicted != self.terms[index] {
                return Err(CertificateError::RecurrenceFailed { index });
            }
        }
        Ok(())
    }

    /// The number of recurrence equations `verify` actually checks. Zero means
    /// the certificate is vacuous and `verify` refuses it.
    pub fn equations_checked(&self) -> usize {
        self.terms.len().saturating_sub(self.order)
    }
}

/// Guess a constant-coefficient linear recurrence for `terms` by
/// Berlekamp–Massey over ℚ.
///
/// **This is a guess certified only on the supplied terms and says nothing
/// beyond them.** A returned [`RecurrenceCertificate`] means exactly one thing:
/// the recurrence reproduces every term that was handed in. It is not evidence
/// that the sequence continues that way, and no amount of agreement on a finite
/// prefix makes it so.
///
/// Declines (returns `None`) on empty input, when the minimal linear complexity
/// found exceeds `floor(len / 2)` — the point past which the fit has as many
/// free parameters as equations and is no longer informative — or when the
/// fitted recurrence fails its own `verify`.
pub fn guess_linear_recurrence(terms: &[BigRational]) -> Option<RecurrenceCertificate> {
    if terms.is_empty() {
        return None;
    }
    let connection = berlekamp_massey(terms);
    let degree = connection.len() - 1;
    if degree > terms.len() / 2 {
        return None;
    }
    let coefficients: Vec<BigRational> = connection[1..].iter().map(|c| -c).collect();
    let certificate = RecurrenceCertificate::new(coefficients, terms.to_vec());
    certificate.verify().ok()?;
    Some(certificate)
}

/// The Berlekamp–Massey connection polynomial `C` of `terms` over ℚ, returned
/// least-significant first with `C[0] = 1` and length `L + 1` for the minimal
/// linear complexity `L`. The generating relation is
/// `Σ_{i=0..=L} C[i] · s_{n−i} = 0` for `n ≥ L`.
fn berlekamp_massey(terms: &[BigRational]) -> Vec<BigRational> {
    let count = terms.len();
    let mut connection = vec![zero(); count + 1];
    connection[0] = BigRational::one();
    let mut previous = connection.clone();
    let mut previous_discrepancy = BigRational::one();
    let mut complexity = 0usize;
    let mut shift = 1usize;

    for index in 0..count {
        let mut discrepancy = terms[index].clone();
        for j in 1..=complexity {
            discrepancy += &connection[j] * &terms[index - j];
        }
        if discrepancy.is_zero() {
            shift += 1;
            continue;
        }
        let scale = &discrepancy / &previous_discrepancy;
        let updated: Vec<BigRational> = (0..connection.len())
            .map(|j| {
                if j >= shift {
                    &connection[j] - &scale * &previous[j - shift]
                } else {
                    connection[j].clone()
                }
            })
            .collect();
        if 2 * complexity <= index {
            previous = connection;
            previous_discrepancy = discrepancy;
            complexity = index + 1 - complexity;
            shift = 1;
        } else {
            shift += 1;
        }
        connection = updated;
    }
    connection.truncate(complexity + 1);
    connection
}

/// The rational generating function `p/q` of a constant-coefficient linear
/// recurrence, with its expansion certificate.
///
/// `q(x) = 1 − Σ c_k x^k` and `deg p < order`, so `p/q` expands to exactly the
/// sequence the recurrence generates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RationalGeneratingFunction {
    /// Numerator polynomial, least-significant first.
    pub numerator: Vec<BigRational>,
    /// Denominator polynomial, least-significant first, with `q(0) = 1`.
    pub denominator: Vec<BigRational>,
    /// The terms the generating function is claimed to expand to.
    pub terms: Vec<BigRational>,
    /// The `q · s ≡ p` identity certificate for that expansion.
    pub expansion: TruncationIdentity,
}

impl RationalGeneratingFunction {
    /// Re-derive both halves of the claim: that `q · s ≡ p` modulo
    /// `x^(order+1)`, and that the expansion `s` really is the term sequence.
    ///
    /// # Errors
    ///
    /// Refuses when the inner identity fails, when the inner identity describes
    /// a different `p` or `q` than this object carries, when the truncation
    /// order does not cover every term, or at the first degree where the
    /// expansion and the terms disagree.
    pub fn verify(&self) -> Result<(), CertificateError> {
        self.expansion.verify()?;
        let TruncationIdentity::RationalExpansion {
            numerator,
            denominator,
            expansion,
            order,
        } = &self.expansion
        else {
            return Err(CertificateError::CertificateMismatch);
        };
        if *numerator != self.numerator || *denominator != self.denominator {
            return Err(CertificateError::CertificateMismatch);
        }
        if self.terms.len() != order + 1 {
            return Err(CertificateError::OrderMismatch {
                expected: self.terms.len().saturating_sub(1),
                found: *order,
            });
        }
        for (degree, term) in self.terms.iter().enumerate() {
            if expansion.coefficients()[degree] != *term {
                return Err(CertificateError::IdentityFailed { degree });
            }
        }
        Ok(())
    }
}

/// The rational generating function of a verified linear recurrence.
///
/// Takes `q(x) = 1 − Σ_{k=1..=d} c_k x^k` and `p = (q · A) mod x^d`, where `A`
/// is the term sequence, then expands `p/q` back out and compares against every
/// supplied term — so the returned [`RationalGeneratingFunction`] is certified,
/// not asserted. Its `verify` re-runs both halves independently.
///
/// `None` when the recurrence certificate does not verify, when fewer initial
/// terms are supplied than its order, or when the expansion disagrees with the
/// terms (which cannot happen for a verified recurrence, and is checked anyway).
pub fn rational_generating_function(
    recurrence: &RecurrenceCertificate,
    initial_terms: &[BigRational],
) -> Option<RationalGeneratingFunction> {
    recurrence.verify().ok()?;
    let degree = recurrence.order;
    if initial_terms.is_empty() || initial_terms.len() < degree {
        return None;
    }
    let order = initial_terms.len() - 1;
    let mut denominator = vec![zero(); degree + 1];
    denominator[0] = BigRational::one();
    for (k, coeff) in recurrence.coefficients.iter().enumerate() {
        denominator[k + 1] = -coeff;
    }
    let numerator_len = degree.max(1);
    let mut numerator = truncated_mul(&denominator, initial_terms, order);
    numerator.truncate(numerator_len);
    numerator.resize(numerator_len, zero());

    let (expansion, certificate) =
        FormalPowerSeries::from_rational_function(&numerator, &denominator, order)?;
    for (degree, term) in initial_terms.iter().enumerate() {
        if expansion.coefficients()[degree] != *term {
            return None;
        }
    }
    let result = RationalGeneratingFunction {
        numerator,
        denominator,
        terms: initial_terms.to_vec(),
        expansion: certificate,
    };
    result.verify().ok()?;
    Some(result)
}
