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
    #[must_use]
    pub fn truncated(&self, order: usize) -> FormalPowerSeries {
        Self::from_coefficients(&self.coeffs, order.min(self.order))
    }

    /// Coefficient-wise sum, truncated to the lower of the two orders.
    ///
    /// `uncertified`: re-deriving a sum is the same addition.
    #[must_use]
    pub fn add(&self, other: &FormalPowerSeries) -> FormalPowerSeries {
        let order = self.order.min(other.order);
        let coeffs = (0..=order)
            .map(|i| &self.coeffs[i] + &other.coeffs[i])
            .collect();
        FormalPowerSeries { coeffs, order }
    }

    /// Coefficient-wise difference. `uncertified`, as [`add`](Self::add).
    #[must_use]
    pub fn sub(&self, other: &FormalPowerSeries) -> FormalPowerSeries {
        let order = self.order.min(other.order);
        let coeffs = (0..=order)
            .map(|i| &self.coeffs[i] - &other.coeffs[i])
            .collect();
        FormalPowerSeries { coeffs, order }
    }

    /// Negation. `uncertified`, as [`add`](Self::add).
    #[must_use]
    pub fn neg(&self) -> FormalPowerSeries {
        FormalPowerSeries {
            coeffs: self.coeffs.iter().map(|c| -c).collect(),
            order: self.order,
        }
    }

    /// Scalar multiple. `uncertified`, as [`add`](Self::add).
    #[must_use]
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
    #[must_use]
    pub fn mul(&self, other: &FormalPowerSeries) -> FormalPowerSeries {
        let order = self.order.min(other.order);
        FormalPowerSeries {
            coeffs: truncated_mul(&self.coeffs, &other.coeffs, order),
            order,
        }
    }

    /// Multiply by `x^k`, keeping the same truncation order (so the top `k`
    /// coefficients fall off the end). `uncertified`, as [`add`](Self::add).
    #[must_use]
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
    #[must_use]
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
    #[must_use]
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
        if initial_terms.len() < degree || order < degree {
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
                for (degree, found) in product.iter().enumerate() {
                    let expected = numerator.get(degree).cloned().unwrap_or_else(zero);
                    if *found != expected {
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

#[cfg(test)]
mod tests {
    use super::{
        CertificateError, FormalPowerSeries, RecurrenceCertificate, TruncationIdentity,
        guess_linear_recurrence, rational_generating_function,
    };
    use crate::CasExpr;
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use num_traits::Zero;

    fn r(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    fn q(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn rats(values: &[i64]) -> Vec<BigRational> {
        values.iter().map(|v| r(*v)).collect()
    }

    // ---------------------------------------------------------------- ring ops

    #[test]
    fn add_sub_neg_scale_truncate_to_the_lower_order() {
        let a = FormalPowerSeries::from_coefficients(&rats(&[1, 2, 3, 4]), 3);
        let b = FormalPowerSeries::from_coefficients(&rats(&[5, 5]), 1);
        assert_eq!(a.add(&b).coefficients(), rats(&[6, 7]).as_slice());
        assert_eq!(a.sub(&b).coefficients(), rats(&[-4, -3]).as_slice());
        assert_eq!(a.neg().coefficients(), rats(&[-1, -2, -3, -4]).as_slice());
        assert_eq!(
            a.scale(&r(2)).coefficients(),
            rats(&[2, 4, 6, 8]).as_slice()
        );
        assert_eq!(a.add(&b).order(), 1);
    }

    #[test]
    fn mul_of_one_plus_x_with_one_minus_x_is_one_minus_x_squared() {
        let a = FormalPowerSeries::from_coefficients(&rats(&[1, 1]), 4);
        let b = FormalPowerSeries::from_coefficients(&rats(&[1, -1]), 4);
        assert_eq!(a.mul(&b).coefficients(), rats(&[1, 0, -1, 0, 0]).as_slice());
    }

    #[test]
    fn shift_up_truncates_and_shift_down_requires_divisibility() {
        let a = FormalPowerSeries::from_coefficients(&rats(&[1, 2, 3]), 2);
        assert_eq!(
            a.mul_by_x_pow(1).coefficients(),
            rats(&[0, 1, 2]).as_slice()
        );
        assert!(a.div_by_x_pow(1).is_none(), "constant term is nonzero");
        let shifted = a.mul_by_x_pow(2);
        let back = shifted.div_by_x_pow(2).expect("divisible by x^2");
        assert_eq!(back.coefficients(), rats(&[1]).as_slice());
        assert_eq!(back.order(), 0);
        assert!(a.div_by_x_pow(9).is_none(), "k past the truncation order");
    }

    #[test]
    fn derivative_of_exp_series_is_exp_series_and_integral_inverts_it() {
        let exp =
            FormalPowerSeries::from_coefficients(&[r(1), r(1), q(1, 2), q(1, 6), q(1, 24)], 4);
        let derivative = exp.derivative();
        assert_eq!(derivative.order(), 3);
        assert_eq!(
            derivative.coefficients(),
            [r(1), r(1), q(1, 2), q(1, 6)].as_slice()
        );
        // The integral recovers everything but the constant of integration.
        let integral = derivative.integral();
        assert_eq!(integral.order(), 4);
        assert_eq!(
            integral.coefficients(),
            [r(0), r(1), q(1, 2), q(1, 6), q(1, 24)].as_slice()
        );
        let restored = integral.add(&FormalPowerSeries::one(4));
        assert_eq!(restored.coefficients(), exp.coefficients());
    }

    #[test]
    fn coefficient_past_the_truncation_is_none_not_zero() {
        let a = FormalPowerSeries::from_coefficients(&rats(&[1, 2]), 2);
        assert_eq!(a.coefficient(2), Some(&r(0)));
        assert_eq!(a.coefficient(3), None);
    }

    // -------------------------------------------------------- inverse (cert)

    #[test]
    fn inverse_of_one_minus_x_gives_all_ones() {
        let one_minus_x = FormalPowerSeries::from_coefficients(&rats(&[1, -1]), 8);
        let (inverse, certificate) = one_minus_x.inverse().expect("f(0) = 1 is invertible");
        assert_eq!(inverse.coefficients(), rats(&[1; 9]).as_slice());
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn inverse_declines_when_the_constant_term_vanishes() {
        let x = FormalPowerSeries::identity(4);
        assert!(x.inverse().is_none());
    }

    // ------------------------------------------------- rational generating fns

    #[test]
    fn fibonacci_from_one_over_one_minus_x_minus_x_squared_is_1_1_2_3_5_8_13_21_34_55_89() {
        let (expansion, certificate) =
            FormalPowerSeries::from_rational_function(&rats(&[1]), &rats(&[1, -1, -1]), 10)
                .expect("q(0) = 1");
        assert_eq!(
            expansion.coefficients(),
            rats(&[1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]).as_slice()
        );
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn rational_function_expansion_declines_when_the_denominator_vanishes_at_zero() {
        assert!(
            FormalPowerSeries::from_rational_function(&rats(&[1]), &rats(&[0, 1]), 5).is_none()
        );
    }

    // ------------------------------------------------------------- recurrences

    #[test]
    fn from_recurrence_reproduces_fibonacci_1_1_2_3_5_8_and_certifies_every_term() {
        let recurrence = RecurrenceCertificate::new(rats(&[1, 1]), rats(&[1, 1, 2]));
        let (series, certificate) =
            FormalPowerSeries::from_recurrence(&recurrence, &rats(&[1, 1]), 10)
                .expect("two initial terms for an order-2 recurrence");
        assert_eq!(
            series.coefficients(),
            rats(&[1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]).as_slice()
        );
        assert_eq!(certificate.verify(), Ok(()));
        assert_eq!(certificate.equations_checked(), 9);
    }

    #[test]
    fn from_recurrence_declines_when_the_order_leaves_no_equation_to_check() {
        let recurrence = RecurrenceCertificate::new(rats(&[1, 1]), rats(&[1, 1, 2]));
        assert!(FormalPowerSeries::from_recurrence(&recurrence, &rats(&[1, 1]), 1).is_none());
        assert!(FormalPowerSeries::from_recurrence(&recurrence, &rats(&[1]), 6).is_none());
    }

    #[test]
    fn berlekamp_massey_recovers_fibonacci_as_order_2_with_coefficients_1_1() {
        let terms = rats(&[1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]);
        let guess = guess_linear_recurrence(&terms).expect("fibonacci is linear of order 2");
        assert_eq!(guess.order, 2);
        assert_eq!(guess.coefficients, rats(&[1, 1]));
        assert_eq!(guess.terms_fitted, 12);
        assert_eq!(guess.verify(), Ok(()));
    }

    #[test]
    fn berlekamp_massey_recovers_lucas_2_1_3_4_7_11_as_order_2_with_coefficients_1_1() {
        let terms = rats(&[2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199]);
        let guess = guess_linear_recurrence(&terms).expect("lucas is linear of order 2");
        assert_eq!(guess.order, 2);
        assert_eq!(guess.coefficients, rats(&[1, 1]));
        assert_eq!(guess.verify(), Ok(()));
    }

    #[test]
    fn berlekamp_massey_recovers_padovan_as_order_3_with_coefficients_0_1_1() {
        let terms = rats(&[1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28, 37]);
        let guess = guess_linear_recurrence(&terms).expect("padovan is linear of order 3");
        assert_eq!(guess.order, 3);
        assert_eq!(guess.coefficients, rats(&[0, 1, 1]));
        assert_eq!(guess.verify(), Ok(()));
    }

    #[test]
    fn berlekamp_massey_declines_on_the_primes_which_satisfy_no_short_recurrence() {
        let primes = rats(&[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]);
        assert_eq!(guess_linear_recurrence(&primes), None);
    }

    #[test]
    fn berlekamp_massey_declines_on_the_empty_sequence() {
        assert_eq!(guess_linear_recurrence(&[]), None);
    }

    #[test]
    fn rational_generating_function_of_fibonacci_is_one_over_one_minus_x_minus_x_squared() {
        let terms = rats(&[1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]);
        let guess = guess_linear_recurrence(&terms).expect("order 2");
        let generating = rational_generating_function(&guess, &terms).expect("expansion agrees");
        assert_eq!(generating.numerator, rats(&[1, 0]));
        assert_eq!(generating.denominator, rats(&[1, -1, -1]));
        assert_eq!(generating.verify(), Ok(()));
    }

    #[test]
    fn rational_generating_function_of_padovan_expands_back_to_every_term() {
        let terms = rats(&[1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28, 37]);
        let guess = guess_linear_recurrence(&terms).expect("order 3");
        let generating = rational_generating_function(&guess, &terms).expect("expansion agrees");
        assert_eq!(generating.denominator, rats(&[1, 0, -1, -1]));
        assert_eq!(generating.verify(), Ok(()));
        let (expansion, certificate) = FormalPowerSeries::from_rational_function(
            &generating.numerator,
            &generating.denominator,
            terms.len() - 1,
        )
        .expect("q(0) = 1");
        assert_eq!(certificate.verify(), Ok(()));
        assert_eq!(expansion.coefficients(), terms.as_slice());
    }

    #[test]
    fn rational_generating_function_refuses_an_unverifiable_recurrence() {
        let forged = RecurrenceCertificate::new(rats(&[1, 1]), rats(&[1, 1, 5, 9]));
        assert_eq!(
            rational_generating_function(&forged, &rats(&[1, 1, 5, 9])),
            None
        );
    }

    // ---------------------------------------------------- reversion / Catalan

    #[test]
    fn catalan_via_reversion_of_x_minus_x_squared_is_1_1_2_5_14_42_132_429() {
        let f = FormalPowerSeries::from_coefficients(&rats(&[0, 1, -1]), 8);
        let (g, certificate) = f.reversion().expect("f(0) = 0 and f'(0) = 1");
        assert_eq!(
            g.coefficients(),
            rats(&[0, 1, 1, 2, 5, 14, 42, 132, 429]).as_slice()
        );
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn catalan_reversion_verified_by_composing_back_to_x() {
        let f = FormalPowerSeries::from_coefficients(&rats(&[0, 1, -1]), 8);
        let (g, _) = f.reversion().expect("revertible");
        let composed = f.compose(&g).expect("g(0) = 0");
        let mut expected = vec![BigRational::zero(); 9];
        expected[1] = r(1);
        assert_eq!(composed.coefficients(), expected.as_slice());
    }

    #[test]
    fn reversion_declines_without_a_vanishing_constant_or_a_nonzero_linear_term() {
        let constant_nonzero = FormalPowerSeries::from_coefficients(&rats(&[1, 1]), 4);
        assert!(constant_nonzero.reversion().is_none());
        let linear_zero = FormalPowerSeries::from_coefficients(&rats(&[0, 0, 1]), 4);
        assert!(linear_zero.reversion().is_none());
    }

    // -------------------------------------------- reuse of the CasExpr engine

    #[test]
    fn exp_coefficients_from_the_cas_expansion_are_one_over_n_factorial() {
        let exp = CasExpr::var("x").exp();
        let series =
            FormalPowerSeries::from_cas_expr(&exp, "x", 8).expect("exp is in the series fragment");
        assert_eq!(
            series.coefficients(),
            [
                r(1),
                r(1),
                q(1, 2),
                q(1, 6),
                q(1, 24),
                q(1, 120),
                q(1, 720),
                q(1, 5040),
                q(1, 40320),
            ]
            .as_slice()
        );
    }

    #[test]
    fn compose_exp_with_x_squared_matches_the_direct_expansion_of_exp_x_squared() {
        let exp = FormalPowerSeries::from_cas_expr(&CasExpr::var("x").exp(), "x", 8)
            .expect("exp expands");
        let x_squared = FormalPowerSeries::from_coefficients(&rats(&[0, 0, 1]), 8);
        let composed = exp
            .compose(&x_squared)
            .expect("inner constant term is zero");
        let direct = FormalPowerSeries::from_cas_expr(
            &(CasExpr::var("x") * CasExpr::var("x")).exp(),
            "x",
            8,
        )
        .expect("exp(x^2) expands");
        assert_eq!(composed.coefficients(), direct.coefficients());
        assert_eq!(
            composed.coefficients(),
            [
                r(1),
                r(0),
                r(1),
                r(0),
                q(1, 2),
                r(0),
                q(1, 6),
                r(0),
                q(1, 24),
            ]
            .as_slice()
        );
    }

    #[test]
    fn compose_declines_when_the_inner_series_has_a_nonzero_constant_term() {
        let outer = FormalPowerSeries::from_coefficients(&rats(&[1, 1, 1]), 2);
        let inner = FormalPowerSeries::from_coefficients(&rats(&[1, 1]), 2);
        assert!(outer.compose(&inner).is_none());
    }

    // ------------------------------------------------------- forged evidence
    //
    // Each of these breaks exactly one thing and names the guard that catches
    // it, so a deleted guard shows up as a single dead test.

    #[test]
    fn forged_inverse_with_a_wrong_coefficient_is_refused_as_identity_failure() {
        let one_minus_x = FormalPowerSeries::from_coefficients(&rats(&[1, -1]), 6);
        let (inverse, _) = one_minus_x.inverse().expect("invertible");
        let mut forged = inverse.coefficients().to_vec();
        forged[3] = r(7);
        let certificate = TruncationIdentity::Inverse {
            series: one_minus_x,
            inverse: FormalPowerSeries::from_coefficients(&forged, 6),
            order: 6,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::IdentityFailed { degree: 3 })
        );
    }

    #[test]
    fn forged_inverse_claiming_a_lower_truncation_order_is_refused_as_order_mismatch() {
        // The coefficients are correct; only the declared order is wrong, so
        // nothing but the order guard can catch this.
        let one_minus_x = FormalPowerSeries::from_coefficients(&rats(&[1, -1]), 6);
        let (inverse, _) = one_minus_x.inverse().expect("invertible");
        let certificate = TruncationIdentity::Inverse {
            series: one_minus_x,
            inverse,
            order: 5,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::OrderMismatch {
                expected: 5,
                found: 6
            })
        );
    }

    #[test]
    fn forged_inverse_of_a_series_vanishing_at_zero_is_refused_as_a_degenerate_term() {
        let certificate = TruncationIdentity::Inverse {
            series: FormalPowerSeries::from_coefficients(&rats(&[0, 1]), 3),
            inverse: FormalPowerSeries::from_coefficients(&rats(&[0, 1]), 3),
            order: 3,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::DegenerateTerm { degree: 0 })
        );
    }

    #[test]
    fn forged_reversion_of_a_series_not_vanishing_at_zero_is_refused_as_a_degenerate_term() {
        let certificate = TruncationIdentity::Reversion {
            series: FormalPowerSeries::from_coefficients(&rats(&[1, 1]), 3),
            reversion: FormalPowerSeries::from_coefficients(&rats(&[0, 1]), 3),
            order: 3,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::DegenerateTerm { degree: 0 })
        );
    }

    #[test]
    fn forged_reversion_of_a_series_with_no_linear_term_is_refused_at_degree_one() {
        let certificate = TruncationIdentity::Reversion {
            series: FormalPowerSeries::from_coefficients(&rats(&[0, 0, 1]), 3),
            reversion: FormalPowerSeries::from_coefficients(&rats(&[0, 1]), 3),
            order: 3,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::DegenerateTerm { degree: 1 })
        );
    }

    #[test]
    fn forged_reversion_with_a_wrong_coefficient_is_refused_as_identity_failure() {
        let f = FormalPowerSeries::from_coefficients(&rats(&[0, 1, -1]), 6);
        let (g, _) = f.reversion().expect("revertible");
        let mut forged = g.coefficients().to_vec();
        forged[4] = r(6); // the true Catalan coefficient here is 5
        let certificate = TruncationIdentity::Reversion {
            series: f,
            reversion: FormalPowerSeries::from_coefficients(&forged, 6),
            order: 6,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::IdentityFailed { degree: 4 })
        );
    }

    #[test]
    fn forged_rational_expansion_with_a_numerator_past_the_truncation_is_refused() {
        // q·s ≡ p holds over every degree the check can see; the only defect is
        // that the numerator carries data the check never examines.
        let certificate = TruncationIdentity::RationalExpansion {
            numerator: rats(&[1, 0, 0, 0, 0]),
            denominator: rats(&[1, -1]),
            expansion: FormalPowerSeries::from_coefficients(&rats(&[1, 1, 1, 1]), 3),
            order: 3,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::DataPastTruncation {
                supplied: 5,
                order: 3
            })
        );
    }

    #[test]
    fn forged_rational_expansion_with_a_vanishing_denominator_at_zero_is_refused() {
        // x·(1+x+x²+x³) ≡ x+x²+x³ mod x⁴, so the identity itself holds; only
        // the q(0) ≠ 0 side condition fails.
        let certificate = TruncationIdentity::RationalExpansion {
            numerator: rats(&[0, 1, 1, 1]),
            denominator: rats(&[0, 1]),
            expansion: FormalPowerSeries::from_coefficients(&rats(&[1, 1, 1, 1]), 3),
            order: 3,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::DegenerateTerm { degree: 0 })
        );
    }

    #[test]
    fn forged_rational_expansion_with_an_empty_denominator_is_refused() {
        let certificate = TruncationIdentity::RationalExpansion {
            numerator: rats(&[1]),
            denominator: Vec::new(),
            expansion: FormalPowerSeries::from_coefficients(&rats(&[1]), 0),
            order: 0,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::EmptyDenominator)
        );
    }

    #[test]
    fn forged_rational_expansion_with_a_wrong_coefficient_is_refused_as_identity_failure() {
        let certificate = TruncationIdentity::RationalExpansion {
            numerator: rats(&[1, 0, 0, 0]),
            denominator: rats(&[1, -1]),
            expansion: FormalPowerSeries::from_coefficients(&rats(&[1, 1, 3, 1]), 3),
            order: 3,
        };
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::IdentityFailed { degree: 2 })
        );
    }

    #[test]
    fn forged_recurrence_with_wrong_coefficients_is_refused_at_the_first_bad_term() {
        let certificate = RecurrenceCertificate::new(rats(&[2, 1]), rats(&[1, 1, 2, 3, 5, 8, 13]));
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::RecurrenceFailed { index: 2 })
        );
    }

    #[test]
    fn forged_recurrence_with_a_wrong_term_is_refused_at_that_term() {
        let certificate = RecurrenceCertificate::new(rats(&[1, 1]), rats(&[1, 1, 2, 3, 5, 9, 13]));
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::RecurrenceFailed { index: 5 })
        );
    }

    #[test]
    fn forged_recurrence_with_a_mismatched_declared_order_is_refused() {
        let mut certificate =
            RecurrenceCertificate::new(rats(&[1, 1]), rats(&[1, 1, 2, 3, 5, 8, 13]));
        certificate.order = 3;
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::OrderMismatch {
                expected: 3,
                found: 2
            })
        );
    }

    #[test]
    fn forged_recurrence_with_a_mismatched_fitted_term_count_is_refused() {
        let mut certificate =
            RecurrenceCertificate::new(rats(&[1, 1]), rats(&[1, 1, 2, 3, 5, 8, 13]));
        certificate.terms_fitted = 99;
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::TermCountMismatch {
                declared: 99,
                found: 7
            })
        );
    }

    #[test]
    fn vacuous_recurrence_certificate_with_no_equation_to_check_is_refused() {
        // Two coefficients, two terms: zero equations, so a checker without the
        // vacuity guard would accept anything at all here.
        let certificate = RecurrenceCertificate::new(rats(&[1, 1]), rats(&[7, 11]));
        assert_eq!(certificate.equations_checked(), 0);
        assert_eq!(
            certificate.verify(),
            Err(CertificateError::VacuousRecurrence { order: 2, terms: 2 })
        );
    }

    #[test]
    fn generating_function_whose_inner_certificate_names_a_different_numerator_is_refused() {
        let terms = rats(&[1, 1, 2, 3, 5, 8, 13, 21]);
        let guess = guess_linear_recurrence(&terms).expect("order 2");
        let mut generating = rational_generating_function(&guess, &terms).expect("certified");
        generating.numerator = rats(&[9, 9]);
        assert_eq!(
            generating.verify(),
            Err(CertificateError::CertificateMismatch)
        );
    }

    #[test]
    fn generating_function_whose_terms_do_not_span_the_truncation_is_refused() {
        let terms = rats(&[1, 1, 2, 3, 5, 8, 13, 21]);
        let guess = guess_linear_recurrence(&terms).expect("order 2");
        let mut generating = rational_generating_function(&guess, &terms).expect("certified");
        generating.terms.truncate(4);
        assert_eq!(
            generating.verify(),
            Err(CertificateError::OrderMismatch {
                expected: 3,
                found: 7
            })
        );
    }

    #[test]
    fn generating_function_with_a_forged_term_is_refused_at_that_degree() {
        let terms = rats(&[1, 1, 2, 3, 5, 8, 13, 21]);
        let guess = guess_linear_recurrence(&terms).expect("order 2");
        let mut generating = rational_generating_function(&guess, &terms).expect("certified");
        generating.terms[5] = r(99);
        assert_eq!(
            generating.verify(),
            Err(CertificateError::IdentityFailed { degree: 5 })
        );
    }
}
