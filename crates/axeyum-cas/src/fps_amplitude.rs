//! The **exact** asymptotic amplitude of a rational power series — the constant
//! `C` in `a(n) ~ C·n^(m−1)·ζ^(−n)`, in ℚ or in ℚ(ζ), never a float and never a
//! sampled fit.
//!
//! # What wave three left open, and what this closes
//!
//! [`crate::fps_analytic`] pins the *radius* `ρ` exactly and then labels the
//! amplitude `asymptotic-verified-at-finite-n`: its
//! [`CoefficientAsymptotics`](crate::fps_analytic::CoefficientAsymptotics)
//! normalises three sampled coefficients and reports that the spread shrinks.
//! That is evidence for the form, not the constant, and its own documentation
//! says so.
//!
//! This module produces the constant. For `F = p/q` whose **unique** singularity
//! of minimal modulus is a real pole `ζ` (with `|ζ| = ρ`) of multiplicity `m`,
//!
//! ```text
//! a(n) ~ C · n^(m−1) · ζ^(−n),     C = (−1)^m · p(ζ) / ( ζ^m · s(ζ) · f′(ζ)^m · (m−1)! )
//! ```
//!
//! where `f` is the monic irreducible factor of `q` that `ζ` is a root of, `m`
//! its multiplicity, and `s = q / f^m` the cofactor. Every quantity on the right
//! is an exact element of ℚ (when `ζ` is rational) or of ℚ(ζ) (when it is not),
//! so `C` is too.
//!
//! ## Where the formula comes from
//!
//! Write `q = (z − ζ)^m · r(z)` with `r(ζ) ≠ 0`. Near `ζ`,
//!
//! ```text
//! (1 − z/ζ)^m · F(z) = (−1)^m (z − ζ)^m ζ^(−m) · p(z) / ((z − ζ)^m r(z))
//!                    → A := (−1)^m p(ζ) / (ζ^m r(ζ)),
//! ```
//!
//! and `[z^n] A·(1 − z/ζ)^(−m) = A·binom(n+m−1, m−1)·ζ^(−n) ~ (A/(m−1)!)·n^(m−1)·ζ^(−n)`.
//! Because `q = f^m·s` with `f` monic, `r = s·(f/(z−ζ))^m` and `f/(z−ζ)` at `ζ`
//! is `f′(ζ)`, so `r(ζ) = s(ζ)·f′(ζ)^m` and `C = A/(m−1)!` is the display above.
//! Every other singularity has modulus strictly greater than `ρ`, so its
//! contribution is `o(ρ^(−n))` and the relation is an asymptotic equality.
//!
//! # What the certificate certifies
//!
//! [`AmplitudeCertificate::verify`] re-derives, from the certificate's own data:
//!
//! 1. the nested [`RadiusCertificate`] (so `ρ` is `ρ`);
//! 2. that **exactly one** irreducible factor of `q` attains that radius — two
//!    would mean two singularities sharing a modulus, and the amplitude would not
//!    be a constant at all;
//! 3. that within that factor the minimal modulus is attained by exactly **one**
//!    root, and that root is real — decided exactly, by the simple-root test in
//!    *The uniqueness test* below;
//! 4. that `ζ` is that root, by a Sturm count of one in its bracket, and that
//!    `|ζ| = ρ` because `|ζ|` is a root of the global modulus polynomial inside
//!    the radius's certified bracket, where that polynomial has exactly one;
//! 5. that `f^m · s` reproduces `q`, so `m` really is the multiplicity;
//! 6. that `C` is the value of the display above, recomputed in ℚ or in
//!    ℚ(ζ) = ℚ\[z\]/(f) through [`crate::numberfield::NumberField`];
//! 7. independently, where the inputs fit the machine width, that `C` agrees with
//!    the leading coefficient of the principal part that
//!    [`crate::partial_fractions::partial_fractions`] computes by a *linear
//!    solve* rather than by evaluating a residue — a second algorithm, not a
//!    restatement;
//! 8. a certified bound `τ > ρ` below which no other singularity lies, so the
//!    tail's exponential rate is named and not assumed; and
//! 9. a window of concrete `n`: the exact coefficients from
//!    [`FormalPowerSeries::from_rational_function`] (whose own truncation
//!    identity is re-checked) against `C·n^(m−1)·ζ^(−n)`, with the comparison done
//!    in **interval arithmetic over the pole's bracket** so an irrational `ζ`
//!    needs no floating point.
//!
//! Steps 1–8 are finite algebraic facts, each re-derived. Step 9 is a
//! cross-check, not the evidence: unlike
//! [`CoefficientAsymptotics`](crate::fps_analytic::CoefficientAsymptotics), the
//! asymptotic form here does not rest on the window. It rests on the classical
//! meromorphic expansion, whose every hypothesis — unique dominant pole, its
//! multiplicity, the value of the residue — is a checked item above.
//!
//! # The uniqueness test
//!
//! Step 3 is the one that needs an argument. Let `f` be irreducible of degree `d`
//! with roots `r₁, …, r_d` (distinct, since `f` is irreducible over ℚ), and let
//! `ρ = minᵢ |rᵢ|`. Let
//!
//! ```text
//! R(t) = Res_z( f(z), z^d·f(t/z) ),
//! ```
//!
//! the pairwise-product resultant [`crate::fps_analytic`] already builds, whose
//! roots with multiplicity are exactly the products `rᵢrⱼ`.
//!
//! > **Claim.** `f` has exactly one root of modulus `ρ`, and it is real, **iff**
//! > `ρ²` is a root of `R` of multiplicity exactly one.
//!
//! *Proof.* A pair `(i, j)` contributes `ρ²` only if `|rᵢ||rⱼ| = ρ²`, and since
//! every modulus is at least `ρ`, only if **both** `rᵢ` and `rⱼ` attain `ρ`.
//!
//! (⇐) Suppose the multiplicity is one, so exactly one pair `(i, j)` has
//! `rᵢrⱼ = ρ²`. Roots come in conjugate pairs, so if `rᵢ` attains `ρ` so does
//! `r̄ᵢ`, and `rᵢ·r̄ᵢ = ρ²`; a second attaining root would give a second such pair
//! unless `r̄ᵢ = rᵢ`. Hence the one pair is `(i, i)` with `rᵢ` real, `rᵢ² = ρ²`,
//! so `rᵢ = ±ρ`. If some other root `rₖ ≠ rᵢ` also attained `ρ`, then either
//! `rₖ` is real, forcing `rₖ = −rᵢ` and giving the second pair `(k, k)` with
//! `rₖ² = ρ²`, or `rₖ` is not real and `(k, k̄)` is a second pair. Either way the
//! multiplicity would exceed one.
//!
//! (⇒) Suppose `rᵢ` is the only root of modulus `ρ`. Then it is fixed by
//! conjugation, hence real and equal to `±ρ`, and the only pair of attaining
//! roots is `(i, i)`, so `ρ²` has multiplicity one. ∎
//!
//! The multiplicity is decided without ever naming `ρ²`: it is one exactly when
//! `ρ²` is **not** a root of `D = gcd(R, R′)`, which a Sturm count of `D` over
//! the square of the radius's bracket settles — or, when `ρ` is rational, a
//! single exact evaluation.
//!
//! Two consequences worth stating. A conjugate pair at the minimal modulus —
//! `1/(1+z²)`, whose coefficients are `1, 0, −1, 0, …` — is refused by this test
//! and not averaged. So is `1/(1−z²)` and every other function whose dominant
//! poles are `±ρ`: they are *periodic*, and
//! [`AmplitudeDecline::DominantModulusNotSimple`] names that cause.
//!
//! # What declines
//!
//! - Several factors attaining the radius
//!   ([`AmplitudeDecline::SharedDominantModulus`]).
//! - One factor attaining it at more than one root, or at a non-real root
//!   ([`AmplitudeDecline::DominantModulusNotSimple`]) — periodicity, refused
//!   rather than averaged.
//! - A radius that is infinite (the series is a polynomial) or only bounded below
//!   ([`AmplitudeDecline::RadiusNotUsable`]).
//! - A window whose relative error does not reach the tolerance
//!   ([`AmplitudeDecline::ToleranceExceeded`]) — for which the remedy is a larger
//!   `base`, and the decline says how far off it was. A pole of multiplicity `m`
//!   has relative error `Θ(1/n)`, so `m ≥ 2` needs a base of a few hundred where
//!   `m = 1` converges geometrically.
//!
//! # Reuse
//!
//! [`crate::fps_analytic::radius_of_convergence`] for `ρ` and the factorization,
//! its `pairwise_product_resultant` and two-width Sturm counter for the
//! uniqueness test, [`crate::numberfield::NumberField`] for ℚ(ζ) arithmetic and
//! its certified inverse, [`crate::partial_fractions::partial_fractions`] for the
//! independent cross-check, [`crate::enclosure::BigInterval`] for the window, and
//! [`FormalPowerSeries::from_rational_function`] for the exact coefficients.

use axeyum_arith::{QPoly, UnivariatePoly};
use axeyum_ir::{Rational, poly};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::enclosure::BigInterval;
use crate::fps::{CertificateError as SeriesError, FormalPowerSeries};
use crate::fps_analytic::{
    AnalyticDecline, AnalyticError, RadiusCertificate, RadiusOfConvergence, cauchy_upper_bound,
    count_roots_in, pairwise_product_resultant, radius_of_convergence,
};
use crate::numberfield::{Element, NumberField};
use crate::partial_fractions::{partial_fractions, verify_partial_fraction_certificate};

/// The number of consecutive indices in the certificate's cross-check window.
const WINDOW_LEN: usize = 4;

/// The smallest window base a certificate may state. Below this the sampled
/// coefficients are still in the pre-asymptotic regime for every shape this
/// module reaches, so a passing window would say nothing.
const MIN_WINDOW_BASE: usize = 8;

/// The loosest relative error the window may state at any of its samples.
///
/// `verify` refuses a certificate declaring anything looser, so widening the
/// claim buys a forger nothing.
fn tolerance_cap() -> BigRational {
    BigRational::new(BigInt::from(1), BigInt::from(100))
}

/// The largest relative error [`AmplitudeCertificate::verify`] accepts at a
/// window sample, and the tolerance [`dominant_pole_amplitude`] holds itself to.
pub fn amplitude_tolerance() -> BigRational {
    tolerance_cap()
}

/// The number of bisection steps used to push the tail bound `τ` up from the
/// radius bracket toward the next singularity. Purely a tightness knob: any `τ`
/// the Sturm count clears is certified, and a smaller one is merely weaker.
const TAIL_REFINEMENT_STEPS: u32 = 24;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Why an [`AmplitudeCertificate`] was refused.
///
/// One variant per independently reachable guard, so a refusal names the
/// re-derivation that disagreed rather than merely reporting that one did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AmplitudeError {
    /// The nested radius certificate refused itself.
    Radius(AnalyticError),
    /// The certificate names a different function than its radius certificate.
    FunctionMismatch,
    /// The radius is infinite or only bounded below, so there is no dominant
    /// pole to name.
    RadiusNotUsable,
    /// The declared dominant factor is not among the radius certificate's
    /// factors, or its multiplicity there disagrees.
    DominantFactorMismatch,
    /// The number of factors whose modulus polynomial attains the radius is not
    /// one, so the dominant modulus is shared and no single amplitude exists.
    SharedDominantModulus {
        /// How many factors attain it.
        factors: usize,
    },
    /// The factor/cofactor split does not reproduce the reduced denominator.
    CofactorMismatch {
        /// The lowest degree at which the product disagrees.
        degree: usize,
    },
    /// The declared dominant factor is not monic.
    DominantFactorNotMonic,
    /// The declared multiplicity is zero, so nothing is a pole.
    ZeroMultiplicity,
    /// The declared pole is not a root of the dominant factor.
    PoleNotARoot,
    /// The pole's bracket is malformed: not `lower < upper`, or it straddles the
    /// origin so no modulus interval follows from it.
    MalformedPoleBracket,
    /// The pole's bracket does not contain exactly one root of the dominant
    /// factor.
    PoleNotIsolated {
        /// The count the claim needs.
        expected: usize,
        /// The count Sturm reports.
        found: usize,
    },
    /// The pole's modulus is not the certified radius: either it is not a root
    /// of the dominant factor's modulus polynomial, or it falls outside the
    /// radius's certified bracket.
    PoleModulusMismatch,
    /// The dominant factor has a root of smaller modulus than the declared pole,
    /// or none at the pole's modulus at all — so the pole is not the factor's
    /// minimal-modulus root.
    PoleModulusNotMinimal {
        /// How many of the factor's root moduli lie at or below the pole's.
        found: usize,
    },
    /// The pole's minimal polynomial is not the declared dominant factor.
    MinimalPolynomialMismatch,
    /// The squared radius is a multiple root of the dominant factor's
    /// pairwise-product resultant, so several roots share the minimal modulus.
    /// See *The uniqueness test* in the module documentation.
    DominantModulusNotSimple,
    /// The pairwise-product resultant of the dominant factor did not re-derive.
    /// Not a refutation — a refusal to trust the primitive that produced it.
    ResultantDeclined,
    /// The quotient by the dominant factor is not a field: the factor is
    /// reducible, or the reused irreducibility test declined.
    NotAFieldGenerator,
    /// The residue denominator is zero, so the formula has no value.
    ResidueDenominatorVanishes,
    /// The recomputed amplitude disagrees with the carried one.
    AmplitudeMismatch,
    /// The carried amplitude is zero, which no simple dominant pole produces.
    AmplitudeIsZero,
    /// The carried amplitude's shape does not match the pole's: a rational
    /// amplitude for an algebraic pole, or coefficients of the wrong length.
    AmplitudeShapeMismatch,
    /// The independent partial-fraction cross-check reached a different leading
    /// principal-part coefficient.
    PartialFractionDisagrees,
    /// The declared tail bound is not above the radius bracket.
    TailBoundNotAboveRadius,
    /// A singularity lies at or below the declared tail bound.
    TailBoundNotCertified {
        /// How many further moduli Sturm found inside the claimed gap.
        found: usize,
    },
    /// The window indices are not consecutive from a large enough base, or there
    /// are the wrong number of them.
    MalformedWindow,
    /// A recomputed coefficient disagrees with the carried one.
    CoefficientMismatch {
        /// Which sample.
        index: usize,
    },
    /// A recomputed relative-error bound disagrees with the carried one.
    ErrorBoundMismatch {
        /// Which sample.
        index: usize,
    },
    /// The relative-error bound at the last sample exceeds the one at the first,
    /// so the window shows no convergence.
    ErrorDoesNotShrink,
    /// A sample's relative-error bound exceeds the stated tolerance.
    ToleranceExceeded {
        /// Which sample.
        index: usize,
    },
    /// The stated tolerance is not positive, or is wider than this module
    /// accepts.
    ToleranceTooLoose,
    /// The reused series expansion refused its own truncation identity.
    SeriesCertificate(SeriesError),
    /// The reused series expansion declined outright.
    SeriesDeclined,
    /// A reused root count declined — a coefficient outside `i128` that the
    /// bignum fallback also could not take, or one of the Sturm machinery's own
    /// caps. Not a refutation.
    SturmDeclined,
    /// Arithmetic in the number field declined.
    FieldArithmeticDeclined,
}

impl core::fmt::Display for AmplitudeError {
    // A flat dispatch: one arm per guard, which is the point — a refusal names
    // the re-derivation that disagreed.
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AmplitudeError::Radius(inner) => write!(f, "radius certificate: {inner}"),
            AmplitudeError::FunctionMismatch => {
                write!(f, "the radius certificate describes a different function")
            }
            AmplitudeError::RadiusNotUsable => {
                write!(f, "the radius is infinite or only bounded below")
            }
            AmplitudeError::DominantFactorMismatch => write!(
                f,
                "the declared dominant factor is not one of the radius certificate's"
            ),
            AmplitudeError::SharedDominantModulus { factors } => write!(
                f,
                "{factors} factors attain the radius, so the dominant modulus is shared"
            ),
            AmplitudeError::CofactorMismatch { degree } => {
                write!(f, "the factor/cofactor split fails at degree {degree}")
            }
            AmplitudeError::DominantFactorNotMonic => {
                write!(f, "the dominant factor is not monic")
            }
            AmplitudeError::ZeroMultiplicity => write!(f, "the declared multiplicity is zero"),
            AmplitudeError::PoleNotARoot => {
                write!(f, "the declared pole is not a root of the dominant factor")
            }
            AmplitudeError::MalformedPoleBracket => write!(f, "malformed pole bracket"),
            AmplitudeError::PoleNotIsolated { expected, found } => write!(
                f,
                "the pole bracket holds {found} roots where the claim needs {expected}"
            ),
            AmplitudeError::PoleModulusMismatch => {
                write!(f, "the pole's modulus is not the certified radius")
            }
            AmplitudeError::PoleModulusNotMinimal { found } => write!(
                f,
                "{found} of the dominant factor's root moduli lie at or below the pole's, not one"
            ),
            AmplitudeError::MinimalPolynomialMismatch => {
                write!(
                    f,
                    "the pole's minimal polynomial is not the dominant factor"
                )
            }
            AmplitudeError::DominantModulusNotSimple => write!(
                f,
                "several roots share the minimal modulus, so no single amplitude exists"
            ),
            AmplitudeError::ResultantDeclined => {
                write!(f, "the pairwise-product resultant did not re-derive")
            }
            AmplitudeError::NotAFieldGenerator => {
                write!(f, "the dominant factor does not generate a number field")
            }
            AmplitudeError::ResidueDenominatorVanishes => {
                write!(f, "the residue denominator vanishes")
            }
            AmplitudeError::AmplitudeMismatch => {
                write!(f, "the recomputed amplitude disagrees with the carried one")
            }
            AmplitudeError::AmplitudeIsZero => write!(f, "the carried amplitude is zero"),
            AmplitudeError::AmplitudeShapeMismatch => {
                write!(
                    f,
                    "the amplitude's representation does not match the pole's"
                )
            }
            AmplitudeError::PartialFractionDisagrees => write!(
                f,
                "the independent partial-fraction computation reached a different amplitude"
            ),
            AmplitudeError::TailBoundNotAboveRadius => {
                write!(f, "the tail bound is not above the radius")
            }
            AmplitudeError::TailBoundNotCertified { found } => {
                write!(f, "{found} further moduli lie inside the claimed tail gap")
            }
            AmplitudeError::MalformedWindow => write!(f, "malformed window indices"),
            AmplitudeError::CoefficientMismatch { index } => {
                write!(f, "sample {index} carries the wrong coefficient")
            }
            AmplitudeError::ErrorBoundMismatch { index } => {
                write!(f, "sample {index} carries the wrong relative-error bound")
            }
            AmplitudeError::ErrorDoesNotShrink => {
                write!(f, "the relative error does not shrink across the window")
            }
            AmplitudeError::ToleranceExceeded { index } => {
                write!(f, "sample {index} exceeds the stated tolerance")
            }
            AmplitudeError::ToleranceTooLoose => write!(f, "the stated tolerance is too loose"),
            AmplitudeError::SeriesCertificate(inner) => write!(f, "series certificate: {inner}"),
            AmplitudeError::SeriesDeclined => write!(f, "the series expansion declined"),
            AmplitudeError::SturmDeclined => write!(f, "the reused root count declined"),
            AmplitudeError::FieldArithmeticDeclined => {
                write!(f, "arithmetic in the number field declined")
            }
        }
    }
}

impl core::error::Error for AmplitudeError {}

/// Why [`dominant_pole_amplitude`] declined to answer.
///
/// A decline is never a refutation: it says this route did not reach an answer,
/// and names which step gave up.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AmplitudeDecline {
    /// The reused radius computation declined.
    Radius(AnalyticDecline),
    /// The radius is infinite (the series is a polynomial) or only bounded
    /// below, so no dominant pole is pinned.
    RadiusNotUsable,
    /// More than one irreducible factor attains the radius: several
    /// singularities share a modulus. Not averaged — declined.
    SharedDominantModulus {
        /// How many factors attain it.
        factors: usize,
    },
    /// The dominant factor attains its minimal modulus at more than one root, or
    /// at a non-real one. This is the periodic case — `1/(1+z^2)`, `1/(1-z^2)` —
    /// where the coefficients oscillate and no single amplitude describes them.
    DominantModulusNotSimple,
    /// The pairwise-product resultant of the dominant factor did not re-derive.
    ResultantDeclined,
    /// A reused Sturm root count declined.
    SturmDeclined,
    /// The dominant factor did not generate a number field: it was found
    /// reducible, or the reused irreducibility test declined.
    NotAFieldGenerator,
    /// Arithmetic in the number field declined — most often a non-invertible
    /// residue denominator.
    FieldArithmeticDeclined,
    /// The independent partial-fraction cross-check disagreed. A bug report, not
    /// an answer.
    PartialFractionDisagrees,
    /// No bound above the radius could be certified free of further
    /// singularities.
    TailBoundDeclined,
    /// The reused series expansion declined.
    SeriesDeclined,
    /// The window base is below this module's floor.
    SampleTooSmall,
    /// The relative error at some window sample is still above
    /// [`amplitude_tolerance`]. The remedy is a larger `base`; the decline
    /// carries what it measured so the caller can see how much larger.
    ToleranceExceeded {
        /// The index at which it was measured.
        n: usize,
        /// The relative-error bound there.
        error: BigRational,
    },
    /// The relative error did not shrink across the window.
    ErrorDoesNotShrink,
    /// The producer built a certificate its own checker refused. A bug report,
    /// not an answer.
    CertificateRefused(AmplitudeError),
}

impl core::fmt::Display for AmplitudeDecline {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AmplitudeDecline::Radius(inner) => write!(f, "radius: {inner}"),
            AmplitudeDecline::RadiusNotUsable => {
                write!(f, "the radius is infinite or only bounded below")
            }
            AmplitudeDecline::SharedDominantModulus { factors } => {
                write!(f, "{factors} factors share the dominant modulus")
            }
            AmplitudeDecline::DominantModulusNotSimple => write!(
                f,
                "several roots share the minimal modulus (the periodic case), so no single amplitude exists"
            ),
            AmplitudeDecline::ResultantDeclined => {
                write!(f, "the pairwise-product resultant did not re-derive")
            }
            AmplitudeDecline::SturmDeclined => write!(f, "a Sturm root count declined"),
            AmplitudeDecline::NotAFieldGenerator => {
                write!(f, "the dominant factor does not generate a number field")
            }
            AmplitudeDecline::FieldArithmeticDeclined => {
                write!(f, "arithmetic in the number field declined")
            }
            AmplitudeDecline::PartialFractionDisagrees => write!(
                f,
                "the independent partial-fraction computation reached a different amplitude"
            ),
            AmplitudeDecline::TailBoundDeclined => {
                write!(f, "no gap above the radius could be certified")
            }
            AmplitudeDecline::SeriesDeclined => write!(f, "the series expansion declined"),
            AmplitudeDecline::SampleTooSmall => write!(f, "the window base is too small"),
            AmplitudeDecline::ToleranceExceeded { n, error } => write!(
                f,
                "relative error {error} at index {n} exceeds tolerance {}",
                amplitude_tolerance()
            ),
            AmplitudeDecline::ErrorDoesNotShrink => {
                write!(f, "the window's relative error does not shrink")
            }
            AmplitudeDecline::CertificateRefused(inner) => {
                write!(f, "the producer's own checker refused: {inner}")
            }
        }
    }
}

impl core::error::Error for AmplitudeDecline {}

// ---------------------------------------------------------------------------
// Polynomial arithmetic over the rationals, least-significant coefficient first
//
// Every routine below delegates to `axeyum_arith`, the shared exact-arithmetic
// layer `crate::fps_analytic` was migrated onto in ADR-1710 slice 4. Nothing
// here re-derives an algorithm; these are the names this module reads with.
// ---------------------------------------------------------------------------

fn zero() -> BigRational {
    BigRational::zero()
}

fn one() -> BigRational {
    BigRational::one()
}

fn trim(poly: Vec<BigRational>) -> Vec<BigRational> {
    axeyum_arith::trim_coefficients(poly)
}

fn degree(poly: &[BigRational]) -> Option<usize> {
    axeyum_arith::slice_degree(poly)
}

fn eval(poly: &[BigRational], at: &BigRational) -> BigRational {
    axeyum_arith::evaluate_slice(poly, at)
}

fn mul(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    QPoly::from_slice(left)
        .mul(&QPoly::from_slice(right))
        .into_coefficients()
}

fn monic(poly: &[BigRational]) -> Vec<BigRational> {
    QPoly::from_slice(poly).monic().into_coefficients()
}

fn derivative(poly: &[BigRational]) -> Vec<BigRational> {
    UnivariatePoly::derivative(&QPoly::from_slice(poly)).into_coefficients()
}

fn div_exact(numerator: &[BigRational], divisor: &[BigRational]) -> Option<Vec<BigRational>> {
    QPoly::from_slice(numerator)
        .div_exact(&QPoly::from_slice(divisor))
        .map(QPoly::into_coefficients)
}

fn poly_gcd(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    QPoly::from_slice(left)
        .gcd(&QPoly::from_slice(right))
        .into_coefficients()
}

fn poly_pow(base: &[BigRational], exponent: u32) -> Vec<BigRational> {
    let mut acc = vec![one()];
    for _ in 0..exponent {
        acc = mul(&acc, base);
    }
    acc
}

fn rat_pow(base: &BigRational, exponent: u32) -> BigRational {
    let mut acc = one();
    for _ in 0..exponent {
        acc *= base;
    }
    acc
}

fn factorial(n: u32) -> BigRational {
    let mut acc = BigInt::from(1u32);
    for k in 2..=u64::from(n) {
        acc *= BigInt::from(k);
    }
    BigRational::from_integer(acc)
}

/// The lowest degree at which two trimmed polynomials disagree, or `None` when
/// they are equal.
fn first_disagreement(left: &[BigRational], right: &[BigRational]) -> Option<usize> {
    let left = trim(left.to_vec());
    let right = trim(right.to_vec());
    let len = left.len().max(right.len());
    let nil = zero();
    (0..len).find(|&index| left.get(index).unwrap_or(&nil) != right.get(index).unwrap_or(&nil))
}

// ---------------------------------------------------------------------------
// The certificate
// ---------------------------------------------------------------------------

/// The dominant pole, pinned exactly.
///
/// Real by construction: a pole with a non-real conjugate partner of the same
/// modulus is refused, not approximated (see *The uniqueness test* in the module
/// documentation).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DominantPole {
    /// The pole is exactly this rational. Reached only when the dominant
    /// irreducible factor is linear, since an irreducible factor of degree at
    /// least two has no rational root.
    Rational(BigRational),
    /// The pole is the unique root of `minimal_polynomial` in the half-open
    /// bracket `(lower, upper]`, which does not straddle the origin.
    Algebraic {
        /// The monic irreducible minimal polynomial — the dominant factor.
        minimal_polynomial: Vec<BigRational>,
        /// The bracket's lower endpoint.
        lower: BigRational,
        /// The bracket's upper endpoint.
        upper: BigRational,
    },
}

impl DominantPole {
    /// The interval the pole is known to lie in: a point for the rational case,
    /// the bracket for the algebraic one.
    fn interval(&self) -> Option<BigInterval> {
        match self {
            DominantPole::Rational(value) => Some(BigInterval::point(value.clone())),
            DominantPole::Algebraic { lower, upper, .. } => {
                BigInterval::new(lower.clone(), upper.clone())
            }
        }
    }

    /// The interval `[lo, hi]` the pole's **modulus** is known to lie in.
    fn modulus_interval(&self) -> Option<(BigRational, BigRational)> {
        match self {
            DominantPole::Rational(value) => Some((value.abs(), value.abs())),
            DominantPole::Algebraic { lower, upper, .. } => {
                if lower.is_positive() {
                    Some((lower.clone(), upper.clone()))
                } else if upper.is_negative() {
                    Some((-upper.clone(), -lower.clone()))
                } else {
                    None
                }
            }
        }
    }
}

/// The amplitude `C`, exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Amplitude {
    /// `C` is exactly this rational.
    Rational(BigRational),
    /// `C = Σ coefficients[k]·ζ^k` in the number field the dominant factor
    /// generates, in the power basis `1, ζ, …, ζ^(d−1)`.
    Algebraic {
        /// The power-basis coordinates, of length the dominant factor's degree.
        coefficients: Vec<BigRational>,
    },
}

/// What is certified about the *next* singularity, which fixes the exponential
/// rate at which the asymptotic form's relative error decays.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TailGap {
    /// The dominant pole is the only singularity: the global modulus polynomial
    /// has no root above the radius at all, searched out to `searched_to`, which
    /// is at least its own Cauchy bound.
    OnlySingularity {
        /// How far the search ran; at least the Cauchy bound of the global
        /// modulus polynomial, so nothing can lie beyond it.
        searched_to: BigRational,
    },
    /// Every singularity other than the dominant pole has modulus strictly
    /// greater than this bound, which is itself strictly greater than the radius.
    AtLeast(BigRational),
}

/// One index of the cross-check window.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmplitudeSample {
    /// The index `n`.
    pub index: usize,
    /// The exact coefficient `a(n)`.
    pub coefficient: BigRational,
    /// A rational upper bound, from interval arithmetic over the pole's bracket,
    /// on `|a(n)·ζ^n / (C·n^(m−1)) − 1|`.
    pub error_bound: BigRational,
}

/// A checkable certificate for `a(n) ~ C·n^(m−1)·ζ^(−n)` with `C` exact.
///
/// The fields are public because a certificate is data, not a promise:
/// [`verify`](AmplitudeCertificate::verify) is the judge. See the module
/// documentation for the nine things it re-derives.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmplitudeCertificate {
    /// The numerator as supplied, least-significant first.
    pub numerator: Vec<BigRational>,
    /// The denominator as supplied, least-significant first, with a nonzero
    /// constant term.
    pub denominator: Vec<BigRational>,
    /// The certified radius the dominance argument rests on.
    pub radius: RadiusCertificate,
    /// The monic irreducible factor of the reduced denominator that the pole is a
    /// root of.
    pub dominant_factor: Vec<BigRational>,
    /// Its multiplicity `m` in the reduced denominator: the order of the pole.
    pub multiplicity: u32,
    /// The cofactor `s` with `dominant_factor^multiplicity · s` the reduced
    /// denominator.
    pub cofactor: Vec<BigRational>,
    /// The dominant pole `ζ`.
    pub pole: DominantPole,
    /// The amplitude `C`.
    pub amplitude: Amplitude,
    /// What is certified about the next singularity.
    pub tail: TailGap,
    /// The cross-check window, at consecutive indices.
    pub samples: Vec<AmplitudeSample>,
    /// The largest relative error the window claims. `verify` refuses anything
    /// looser than this module's own cap.
    pub tolerance: BigRational,
}

/// The three rationals a radius certificate offers a dominance argument: the
/// bracket around the radius, and the cut below which no other factor may have a
/// modulus.
fn radius_brackets(
    radius: &RadiusOfConvergence,
) -> Result<(BigRational, BigRational, BigRational), AmplitudeError> {
    match radius {
        RadiusOfConvergence::Exact(value) => Ok((value.clone(), value.clone(), value.clone())),
        RadiusOfConvergence::Algebraic(data) => Ok((
            data.lower.clone(),
            data.upper.clone(),
            data.coarse_upper.clone(),
        )),
        RadiusOfConvergence::Infinite | RadiusOfConvergence::LowerBound(_) => {
            Err(AmplitudeError::RadiusNotUsable)
        }
    }
}

/// `G = Π g` over the radius certificate's factors. `None` when any factor is
/// bound-only, so a dominance claim can never rest on an incomplete product.
fn global_modulus_polynomial(radius: &RadiusCertificate) -> Option<Vec<BigRational>> {
    let mut global = vec![one()];
    for bound in &radius.factors {
        if bound.modulus_polynomial.is_empty() {
            return None;
        }
        global = mul(&global, &bound.modulus_polynomial);
    }
    Some(global)
}

/// Whether the minimal modulus of `factor`'s roots is attained by exactly one
/// root — which then must be real. See *The uniqueness test* in the module
/// documentation for the proof.
///
/// `modulus_upper` must be an upper bound on that minimal modulus. `None` when
/// the pairwise-product resultant or a Sturm count declined; `Some(false)` is a
/// refutation, not a decline.
fn minimal_modulus_is_simple(factor: &[BigRational], modulus_upper: &BigRational) -> Option<bool> {
    let resultant = pairwise_product_resultant(factor)?;
    let multiple = poly_gcd(&resultant, &derivative(&resultant));
    match degree(&multiple) {
        // `gcd(R, R')` is a nonzero constant: every root of `R` is simple, so in
        // particular the squared minimal modulus is.
        Some(0) => Some(true),
        None => None,
        Some(_) => {
            let squared = modulus_upper * modulus_upper;
            let count = count_roots_in(&multiple, &zero(), &squared)?;
            Some(count == 0)
        }
    }
}

/// An enclosure of the amplitude, given an enclosure of the pole.
fn amplitude_interval(amplitude: &Amplitude, pole: &BigInterval) -> BigInterval {
    match amplitude {
        Amplitude::Rational(value) => BigInterval::point(value.clone()),
        Amplitude::Algebraic { coefficients } => {
            let mut acc = BigInterval::point(zero());
            for coeff in coefficients.iter().rev() {
                acc = acc.mul(pole).add(&BigInterval::point(coeff.clone()));
            }
            acc
        }
    }
}

/// A rational upper bound on `|a(n)·ζ^n / (C·n^k) − 1|`, from interval
/// arithmetic over the pole's bracket. `None` when the amplitude's enclosure
/// straddles zero, so the ratio has no bound.
fn relative_error_bound(
    coefficient: &BigRational,
    pole: &BigInterval,
    amplitude: &BigInterval,
    index: usize,
    exponent: u32,
) -> Option<BigRational> {
    let power = pole.pow(u32::try_from(index).ok()?);
    let numerator = BigInterval::point(coefficient.clone()).mul(&power);
    let scale = rat_pow(&BigRational::from_integer(BigInt::from(index)), exponent);
    let denominator = amplitude.scale(&scale);
    let ratio = numerator.div(&denominator)?;
    let error = ratio.sub(&BigInterval::point(one()));
    let low = error.lo().abs();
    let high = error.hi().abs();
    Some(if low > high { low } else { high })
}

impl AmplitudeCertificate {
    /// The polynomial-growth exponent `k = m − 1` in `a(n) ~ C·n^k·ζ^(−n)`.
    pub fn exponent(&self) -> u32 {
        self.multiplicity.saturating_sub(1)
    }

    /// Re-derive every step of the claim from the certificate's own data.
    ///
    /// The nine steps are listed in the module documentation. None of them
    /// consults how the answer was found.
    ///
    /// # Errors
    ///
    /// One [`AmplitudeError`] per guard; see that type. An
    /// [`AmplitudeError::SturmDeclined`], [`AmplitudeError::ResultantDeclined`]
    /// or [`AmplitudeError::SeriesDeclined`] is a refusal to trust a reused
    /// primitive, not a refutation of the amplitude.
    pub fn verify(&self) -> Result<(), AmplitudeError> {
        self.radius.verify().map_err(AmplitudeError::Radius)?;
        let numerator = trim(self.numerator.clone());
        let denominator = trim(self.denominator.clone());
        if self.radius.numerator != numerator || self.radius.denominator != denominator {
            return Err(AmplitudeError::FunctionMismatch);
        }
        if self.multiplicity == 0 {
            return Err(AmplitudeError::ZeroMultiplicity);
        }
        if !self.tolerance.is_positive() || self.tolerance > tolerance_cap() {
            return Err(AmplitudeError::ToleranceTooLoose);
        }
        let (bracket_lower, bracket_upper, cut) = radius_brackets(&self.radius.radius)?;

        let dominant = self.verify_dominance(&cut)?;
        self.verify_split()?;
        let pole = self.verify_pole(dominant, &bracket_lower, &bracket_upper)?;
        // The cross-check runs BEFORE the residue recomputation on purpose: it
        // is the second, independent route to `C`, and putting it first is what
        // makes both guards reachable by a test rather than one shadowing the
        // other.
        self.verify_partial_fraction_cross_check()?;
        self.verify_amplitude()?;
        self.verify_tail(&bracket_upper)?;
        self.verify_window(&pole)
    }

    /// Exactly one irreducible factor attains the radius, and it is the declared
    /// dominant factor with the declared multiplicity.
    ///
    /// `cut` is the radius certificate's own upper cut: the exact radius, or the
    /// coarse Sturm bracket's upper endpoint. Below it the global modulus
    /// polynomial has exactly one root, so a factor contributing a root there is
    /// contributing the radius itself.
    fn verify_dominance(&self, cut: &BigRational) -> Result<usize, AmplitudeError> {
        let declared = trim(self.dominant_factor.clone());
        let declared_degree = degree(&declared).ok_or(AmplitudeError::DominantFactorMismatch)?;
        if declared_degree == 0 || !declared[declared_degree].is_one() {
            return Err(AmplitudeError::DominantFactorNotMonic);
        }
        let mut dominant: Option<usize> = None;
        let mut attaining = 0usize;
        for (index, bound) in self.radius.factors.iter().enumerate() {
            if bound.modulus_polynomial.is_empty() {
                return Err(AmplitudeError::RadiusNotUsable);
            }
            let count = count_roots_in(&bound.modulus_polynomial, &zero(), cut)
                .ok_or(AmplitudeError::SturmDeclined)?;
            if count >= 1 {
                attaining += 1;
                dominant = Some(index);
            }
        }
        if attaining != 1 {
            return Err(AmplitudeError::SharedDominantModulus { factors: attaining });
        }
        let index = dominant.ok_or(AmplitudeError::SharedDominantModulus { factors: 0 })?;
        let bound = &self.radius.factors[index];
        if monic(&bound.factor) != declared || bound.multiplicity != self.multiplicity {
            return Err(AmplitudeError::DominantFactorMismatch);
        }
        Ok(index)
    }

    /// `dominant_factor^multiplicity · cofactor` is the reduced denominator, so
    /// `multiplicity` really is the pole's order and `cofactor` really is what is
    /// left over.
    fn verify_split(&self) -> Result<(), AmplitudeError> {
        let rebuilt = mul(
            &poly_pow(&self.dominant_factor, self.multiplicity),
            &self.cofactor,
        );
        if let Some(degree) = first_disagreement(&rebuilt, &self.radius.reduced_denominator) {
            return Err(AmplitudeError::CofactorMismatch { degree });
        }
        Ok(())
    }

    /// The pole is a root of the dominant factor, is isolated in its bracket, has
    /// the smallest modulus among that factor's roots, and attains it alone.
    ///
    /// Returns the interval the pole is enclosed in, for the window.
    fn verify_pole(
        &self,
        dominant: usize,
        bracket_lower: &BigRational,
        bracket_upper: &BigRational,
    ) -> Result<BigInterval, AmplitudeError> {
        let factor = trim(self.dominant_factor.clone());
        let bound = &self.radius.factors[dominant];

        match &self.pole {
            DominantPole::Rational(value) => {
                if !eval(&factor, value).is_zero() {
                    return Err(AmplitudeError::PoleNotARoot);
                }
                // The modulus of a rational pole is exact, so it can be checked
                // against the factor's modulus polynomial directly rather than
                // through the theorem that relates the two.
                if !eval(&bound.modulus_polynomial, &value.abs()).is_zero() {
                    return Err(AmplitudeError::PoleModulusMismatch);
                }
            }
            DominantPole::Algebraic {
                minimal_polynomial,
                lower,
                upper,
            } => {
                if trim(minimal_polynomial.clone()) != factor {
                    return Err(AmplitudeError::MinimalPolynomialMismatch);
                }
                if lower >= upper || !(lower.is_positive() || upper.is_negative()) {
                    return Err(AmplitudeError::MalformedPoleBracket);
                }
                let count =
                    count_roots_in(&factor, lower, upper).ok_or(AmplitudeError::SturmDeclined)?;
                if count != 1 {
                    return Err(AmplitudeError::PoleNotIsolated {
                        expected: 1,
                        found: count,
                    });
                }
            }
        }

        let (modulus_lower, modulus_upper) = self
            .pole
            .modulus_interval()
            .ok_or(AmplitudeError::MalformedPoleBracket)?;
        if !modulus_lower.is_positive() {
            return Err(AmplitudeError::PoleModulusMismatch);
        }
        if modulus_lower < *bracket_lower || modulus_upper > *bracket_upper {
            return Err(AmplitudeError::PoleModulusMismatch);
        }
        // Exactly one modulus of this factor's roots lies at or below the pole's
        // own, so every other root of the factor has modulus above the bracket —
        // except possibly one sharing the pole's modulus exactly, which the
        // simplicity test below is what rules out.
        let below = count_roots_in(&bound.modulus_polynomial, &zero(), &modulus_upper)
            .ok_or(AmplitudeError::SturmDeclined)?;
        if below != 1 {
            return Err(AmplitudeError::PoleModulusNotMinimal { found: below });
        }
        match minimal_modulus_is_simple(&factor, &modulus_upper) {
            None => return Err(AmplitudeError::ResultantDeclined),
            Some(false) => return Err(AmplitudeError::DominantModulusNotSimple),
            Some(true) => {}
        }

        self.pole
            .interval()
            .ok_or(AmplitudeError::MalformedPoleBracket)
    }

    /// `C` is the value the residue formula gives, recomputed in the rationals or
    /// in the number field the dominant factor generates.
    fn verify_amplitude(&self) -> Result<(), AmplitudeError> {
        let factor = trim(self.dominant_factor.clone());
        let slope = derivative(&factor);
        let multiplicity = self.multiplicity;
        let scale = factorial(multiplicity - 1);

        match (&self.pole, &self.amplitude) {
            (DominantPole::Rational(pole), Amplitude::Rational(claimed)) => {
                let denominator = rat_pow(pole, multiplicity)
                    * eval(&self.cofactor, pole)
                    * rat_pow(&eval(&slope, pole), multiplicity)
                    * scale;
                if denominator.is_zero() {
                    return Err(AmplitudeError::ResidueDenominatorVanishes);
                }
                let mut value = eval(&self.radius.reduced_numerator, pole) / denominator;
                if multiplicity % 2 == 1 {
                    value = -value;
                }
                if value.is_zero() {
                    return Err(AmplitudeError::AmplitudeIsZero);
                }
                if value != *claimed {
                    return Err(AmplitudeError::AmplitudeMismatch);
                }
                Ok(())
            }
            (DominantPole::Algebraic { .. }, Amplitude::Algebraic { coefficients }) => {
                // `NumberField::new` re-checks that the factor is monic and
                // irreducible over the rationals, so the power basis this works
                // in is a basis.
                let field =
                    NumberField::new(&factor).map_err(|_| AmplitudeError::NotAFieldGenerator)?;
                if coefficients.len() != field.degree() {
                    return Err(AmplitudeError::AmplitudeShapeMismatch);
                }
                let pole = field.generator();
                let denominator = pole
                    .pow(multiplicity)
                    .mul(&field.element(&self.cofactor))
                    .and_then(|value| value.mul(&field.element(&slope).pow(multiplicity)))
                    .ok_or(AmplitudeError::FieldArithmeticDeclined)?;
                if denominator.is_zero() {
                    return Err(AmplitudeError::ResidueDenominatorVanishes);
                }
                let (inverse, inverse_certificate) = denominator
                    .inverse()
                    .ok_or(AmplitudeError::FieldArithmeticDeclined)?;
                inverse_certificate
                    .verify()
                    .map_err(|_| AmplitudeError::FieldArithmeticDeclined)?;
                let mut value = field
                    .element(&self.radius.reduced_numerator)
                    .mul(&inverse)
                    .ok_or(AmplitudeError::FieldArithmeticDeclined)?
                    .scale(&(one() / scale));
                if multiplicity % 2 == 1 {
                    value = value.neg();
                }
                if value.is_zero() {
                    return Err(AmplitudeError::AmplitudeIsZero);
                }
                if value.coeffs() != coefficients.as_slice() {
                    return Err(AmplitudeError::AmplitudeMismatch);
                }
                Ok(())
            }
            _ => Err(AmplitudeError::AmplitudeShapeMismatch),
        }
    }

    /// The independent cross-check: for a rational pole whose data fits the
    /// machine width, [`crate::partial_fractions::partial_fractions`] reaches the
    /// leading principal-part coefficient by a **linear solve** over the whole
    /// decomposition, where this module evaluates a residue. Two algorithms, one
    /// number.
    ///
    /// A decline from that route is not a refutation, so it is skipped; a
    /// disagreement is [`AmplitudeError::PartialFractionDisagrees`].
    fn verify_partial_fraction_cross_check(&self) -> Result<(), AmplitudeError> {
        let (DominantPole::Rational(pole), Amplitude::Rational(claimed)) =
            (&self.pole, &self.amplitude)
        else {
            return Ok(());
        };
        let Some(numerator) = to_machine(&self.radius.reduced_numerator) else {
            return Ok(());
        };
        let Some(denominator) = to_machine(&self.radius.reduced_denominator) else {
            return Ok(());
        };
        let Some(certificate) = partial_fractions(&numerator, &denominator) else {
            return Ok(());
        };
        if verify_partial_fraction_certificate(&certificate) != Some(true) {
            return Ok(());
        }
        let mut leading: Option<BigRational> = None;
        for term in &certificate.terms {
            if poly::rat_degree(&term.factor) != Some(1) || term.power != self.multiplicity {
                continue;
            }
            let constant = term.factor[0].to_big_rational();
            let slope = term.factor[1].to_big_rational();
            if slope.is_zero() || -constant / &slope != *pole {
                continue;
            }
            let residue: BigRational = term
                .numerator
                .first()
                .map_or_else(zero, |value| value.to_big_rational());
            if term.numerator.len() > 1 {
                // `deg N < deg factor = 1` makes this unreachable for a
                // well-formed decomposition; a longer numerator means the reused
                // producer changed shape, so decline rather than misread it.
                return Ok(());
            }
            let scale = rat_pow(&slope, self.multiplicity)
                * rat_pow(pole, self.multiplicity)
                * factorial(self.multiplicity - 1);
            if scale.is_zero() {
                return Ok(());
            }
            let mut value = residue / scale;
            if self.multiplicity % 2 == 1 {
                value = -value;
            }
            leading = Some(value);
        }
        match leading {
            Some(value) if value != *claimed => Err(AmplitudeError::PartialFractionDisagrees),
            _ => Ok(()),
        }
    }

    /// The declared gap above the radius really is free of further moduli.
    fn verify_tail(&self, bracket_upper: &BigRational) -> Result<(), AmplitudeError> {
        let global =
            global_modulus_polynomial(&self.radius).ok_or(AmplitudeError::RadiusNotUsable)?;
        let limit = match &self.tail {
            TailGap::AtLeast(bound) => {
                if bound <= bracket_upper {
                    return Err(AmplitudeError::TailBoundNotAboveRadius);
                }
                bound.clone()
            }
            TailGap::OnlySingularity { searched_to } => {
                let cauchy = cauchy_upper_bound(&global).ok_or(AmplitudeError::SturmDeclined)?;
                if searched_to <= bracket_upper || *searched_to < cauchy {
                    return Err(AmplitudeError::TailBoundNotAboveRadius);
                }
                searched_to.clone()
            }
        };
        let found =
            count_roots_in(&global, bracket_upper, &limit).ok_or(AmplitudeError::SturmDeclined)?;
        if found != 0 {
            return Err(AmplitudeError::TailBoundNotCertified { found });
        }
        Ok(())
    }

    /// The window: exact coefficients from the reused expansion, compared with
    /// `C·n^(m−1)·ζ^(−n)` in interval arithmetic over the pole's bracket.
    fn verify_window(&self, pole: &BigInterval) -> Result<(), AmplitudeError> {
        if self.samples.len() != WINDOW_LEN {
            return Err(AmplitudeError::MalformedWindow);
        }
        let base = self.samples[0].index;
        if base < MIN_WINDOW_BASE {
            return Err(AmplitudeError::MalformedWindow);
        }
        for (offset, sample) in self.samples.iter().enumerate() {
            if sample.index != base + offset {
                return Err(AmplitudeError::MalformedWindow);
            }
        }
        let order = self
            .samples
            .last()
            .ok_or(AmplitudeError::MalformedWindow)?
            .index;
        let (series, identity) =
            FormalPowerSeries::from_rational_function(&self.numerator, &self.denominator, order)
                .ok_or(AmplitudeError::SeriesDeclined)?;
        identity
            .verify()
            .map_err(AmplitudeError::SeriesCertificate)?;

        let amplitude = amplitude_interval(&self.amplitude, pole);
        let exponent = self.exponent();
        for (offset, sample) in self.samples.iter().enumerate() {
            let coefficient = series
                .coefficient(sample.index)
                .ok_or(AmplitudeError::SeriesDeclined)?;
            if *coefficient != sample.coefficient {
                return Err(AmplitudeError::CoefficientMismatch { index: offset });
            }
            let bound = relative_error_bound(
                &sample.coefficient,
                pole,
                &amplitude,
                sample.index,
                exponent,
            )
            .ok_or(AmplitudeError::AmplitudeIsZero)?;
            if bound != sample.error_bound {
                return Err(AmplitudeError::ErrorBoundMismatch { index: offset });
            }
            if bound > self.tolerance {
                return Err(AmplitudeError::ToleranceExceeded { index: offset });
            }
        }
        let first = self
            .samples
            .first()
            .ok_or(AmplitudeError::MalformedWindow)?;
        let last = self.samples.last().ok_or(AmplitudeError::MalformedWindow)?;
        if last.error_bound > first.error_bound {
            return Err(AmplitudeError::ErrorDoesNotShrink);
        }
        Ok(())
    }
}

/// Narrow a rational polynomial to the machine width, or `None` when a
/// coefficient does not fit.
fn to_machine(poly: &[BigRational]) -> Option<Vec<Rational>> {
    poly.iter().map(Rational::from_big_rational).collect()
}

// ---------------------------------------------------------------------------
// The producer
// ---------------------------------------------------------------------------

/// Locate the dominant pole inside the radius's bracket, or decline.
///
/// For a rational radius the only candidates are `±ρ`, decided by an exact
/// evaluation. Otherwise the bracket (and its reflection) are Sturm-counted:
/// exactly one of them must hold exactly one root of the factor. Two — `±ρ` both
/// roots — is the periodic case and declines; none means the minimal modulus is
/// attained only by non-real roots, which declines too.
fn locate_pole(
    factor: &[BigRational],
    bracket_lower: &BigRational,
    bracket_upper: &BigRational,
) -> Result<DominantPole, AmplitudeDecline> {
    if bracket_lower == bracket_upper {
        if eval(factor, bracket_lower).is_zero() {
            return Ok(DominantPole::Rational(bracket_lower.clone()));
        }
        let negated = -bracket_lower.clone();
        if eval(factor, &negated).is_zero() {
            return Ok(DominantPole::Rational(negated));
        }
        return Err(AmplitudeDecline::DominantModulusNotSimple);
    }
    let positive = count_roots_in(factor, bracket_lower, bracket_upper)
        .ok_or(AmplitudeDecline::SturmDeclined)?;
    let reflected_lower = -bracket_upper.clone();
    let reflected_upper = -bracket_lower.clone();
    let negative = count_roots_in(factor, &reflected_lower, &reflected_upper)
        .ok_or(AmplitudeDecline::SturmDeclined)?;
    match (positive, negative) {
        (1, 0) => Ok(DominantPole::Algebraic {
            minimal_polynomial: factor.to_vec(),
            lower: bracket_lower.clone(),
            upper: bracket_upper.clone(),
        }),
        (0, 1) => Ok(DominantPole::Algebraic {
            minimal_polynomial: factor.to_vec(),
            lower: reflected_lower,
            upper: reflected_upper,
        }),
        _ => Err(AmplitudeDecline::DominantModulusNotSimple),
    }
}

/// The residue formula, evaluated exactly in the rationals or in the number
/// field the dominant factor generates.
fn compute_amplitude(
    reduced_numerator: &[BigRational],
    factor: &[BigRational],
    cofactor: &[BigRational],
    multiplicity: u32,
    pole: &DominantPole,
) -> Result<Amplitude, AmplitudeDecline> {
    let slope = derivative(factor);
    let scale = factorial(multiplicity - 1);
    match pole {
        DominantPole::Rational(value) => {
            let denominator = rat_pow(value, multiplicity)
                * eval(cofactor, value)
                * rat_pow(&eval(&slope, value), multiplicity)
                * scale;
            if denominator.is_zero() {
                return Err(AmplitudeDecline::FieldArithmeticDeclined);
            }
            let mut amplitude = eval(reduced_numerator, value) / denominator;
            if multiplicity % 2 == 1 {
                amplitude = -amplitude;
            }
            Ok(Amplitude::Rational(amplitude))
        }
        DominantPole::Algebraic { .. } => {
            let field =
                NumberField::new(factor).map_err(|_| AmplitudeDecline::NotAFieldGenerator)?;
            let generator = field.generator();
            let denominator = generator
                .pow(multiplicity)
                .mul(&field.element(cofactor))
                .and_then(|value| value.mul(&field.element(&slope).pow(multiplicity)))
                .ok_or(AmplitudeDecline::FieldArithmeticDeclined)?;
            if denominator.is_zero() {
                return Err(AmplitudeDecline::FieldArithmeticDeclined);
            }
            let (inverse, _) = denominator
                .inverse()
                .ok_or(AmplitudeDecline::FieldArithmeticDeclined)?;
            let mut amplitude: Element = field
                .element(reduced_numerator)
                .mul(&inverse)
                .ok_or(AmplitudeDecline::FieldArithmeticDeclined)?
                .scale(&(one() / scale));
            if multiplicity % 2 == 1 {
                amplitude = amplitude.neg();
            }
            Ok(Amplitude::Algebraic {
                coefficients: amplitude.coeffs().to_vec(),
            })
        }
    }
}

/// Push a certified gap up from the radius toward the next singularity.
///
/// Any bound the Sturm count clears is certified; a smaller one is merely a
/// weaker statement, so the bisection is a tightness knob and never a soundness
/// one.
fn certify_tail(
    radius: &RadiusCertificate,
    bracket_upper: &BigRational,
) -> Result<TailGap, AmplitudeDecline> {
    let global = global_modulus_polynomial(radius).ok_or(AmplitudeDecline::RadiusNotUsable)?;
    let cauchy = cauchy_upper_bound(&global).ok_or(AmplitudeDecline::SturmDeclined)?;
    let searched_to = if cauchy > *bracket_upper {
        cauchy
    } else {
        bracket_upper + one()
    };
    if count_roots_in(&global, bracket_upper, &searched_to)
        .ok_or(AmplitudeDecline::SturmDeclined)?
        == 0
    {
        return Ok(TailGap::OnlySingularity { searched_to });
    }
    let two = BigRational::from_integer(BigInt::from(2));
    let mut low = bracket_upper.clone();
    let mut high = searched_to;
    for _ in 0..TAIL_REFINEMENT_STEPS {
        let mid = (&low + &high) / &two;
        if count_roots_in(&global, bracket_upper, &mid).ok_or(AmplitudeDecline::SturmDeclined)? == 0
        {
            low = mid;
        } else {
            high = mid;
        }
    }
    if low <= *bracket_upper {
        return Err(AmplitudeDecline::TailBoundDeclined);
    }
    Ok(TailGap::AtLeast(low))
}

/// The cross-check window: the exact coefficients at four consecutive indices,
/// each with the relative-error bound interval arithmetic over the pole's
/// bracket gives.
///
/// Split out of [`dominant_pole_amplitude`] so the producer reads as the
/// decision procedure it is; the window is a measurement, not a decision.
fn build_window(
    numerator: &[BigRational],
    denominator: &[BigRational],
    pole: &DominantPole,
    amplitude: &Amplitude,
    exponent: u32,
    base: usize,
    tolerance: &BigRational,
) -> Result<Vec<AmplitudeSample>, AmplitudeDecline> {
    let order = base + WINDOW_LEN - 1;
    let (series, _) = FormalPowerSeries::from_rational_function(numerator, denominator, order)
        .ok_or(AmplitudeDecline::SeriesDeclined)?;
    let pole_interval = pole
        .interval()
        .ok_or(AmplitudeDecline::DominantModulusNotSimple)?;
    let amplitude_interval = amplitude_interval(amplitude, &pole_interval);
    let mut samples = Vec::with_capacity(WINDOW_LEN);
    for offset in 0..WINDOW_LEN {
        let index = base + offset;
        let coefficient = series
            .coefficient(index)
            .ok_or(AmplitudeDecline::SeriesDeclined)?
            .clone();
        let error_bound = relative_error_bound(
            &coefficient,
            &pole_interval,
            &amplitude_interval,
            index,
            exponent,
        )
        .ok_or(AmplitudeDecline::FieldArithmeticDeclined)?;
        if error_bound > *tolerance {
            return Err(AmplitudeDecline::ToleranceExceeded {
                n: index,
                error: error_bound,
            });
        }
        samples.push(AmplitudeSample {
            index,
            coefficient,
            error_bound,
        });
    }
    if samples[WINDOW_LEN - 1].error_bound > samples[0].error_bound {
        return Err(AmplitudeDecline::ErrorDoesNotShrink);
    }
    Ok(samples)
}

/// The exact asymptotic amplitude of the rational power series `p/q`, with a
/// certificate.
///
/// Returns `a(n) ~ C·n^(m−1)·ζ^(−n)` where `ζ` is the unique singularity of
/// minimal modulus, `m` its order, and `C` an **exact** element of the rationals
/// or of the number field `ζ` generates. See the module documentation for what
/// [`AmplitudeCertificate::verify`] re-derives, and for the uniqueness test that
/// makes "unique" a checked fact rather than an assumption.
///
/// `base` is the first index of the cross-check window, which runs over four
/// consecutive indices. A pole of order `m ≥ 2` has relative error `Θ(1/n)`, so
/// it needs a base of a few hundred where a simple pole converges geometrically;
/// [`AmplitudeDecline::ToleranceExceeded`] carries the error it measured so the
/// caller can see how much larger a base to ask for.
///
/// # Errors
///
/// Declines with an [`AmplitudeDecline`] when the radius is infinite or only
/// bounded, when several singularities share the minimal modulus (the periodic
/// case — refused, never averaged), when a reused primitive gives up, or when the
/// window does not reach the tolerance. A decline never means "the amplitude is
/// not what you think"; it means this route did not reach it.
pub fn dominant_pole_amplitude(
    numerator: &[BigRational],
    denominator: &[BigRational],
    base: usize,
) -> Result<AmplitudeCertificate, AmplitudeDecline> {
    if base < MIN_WINDOW_BASE {
        return Err(AmplitudeDecline::SampleTooSmall);
    }
    let radius = radius_of_convergence(numerator, denominator).map_err(AmplitudeDecline::Radius)?;
    let (bracket_lower, bracket_upper, cut) =
        radius_brackets(&radius.radius).map_err(|_| AmplitudeDecline::RadiusNotUsable)?;

    let mut dominant: Option<usize> = None;
    let mut attaining = 0usize;
    for (index, bound) in radius.factors.iter().enumerate() {
        if bound.modulus_polynomial.is_empty() {
            return Err(AmplitudeDecline::RadiusNotUsable);
        }
        let count = count_roots_in(&bound.modulus_polynomial, &zero(), &cut)
            .ok_or(AmplitudeDecline::SturmDeclined)?;
        if count >= 1 {
            attaining += 1;
            dominant = Some(index);
        }
    }
    if attaining != 1 {
        return Err(AmplitudeDecline::SharedDominantModulus { factors: attaining });
    }
    let index = dominant.ok_or(AmplitudeDecline::SharedDominantModulus { factors: 0 })?;
    let bound = &radius.factors[index];
    let factor = monic(&bound.factor);
    let multiplicity = bound.multiplicity;
    if multiplicity == 0 {
        return Err(AmplitudeDecline::CertificateRefused(
            AmplitudeError::ZeroMultiplicity,
        ));
    }
    let cofactor = div_exact(
        &radius.reduced_denominator,
        &poly_pow(&factor, multiplicity),
    )
    .ok_or(AmplitudeDecline::CertificateRefused(
        AmplitudeError::CofactorMismatch { degree: 0 },
    ))?;

    let pole = locate_pole(&factor, &bracket_lower, &bracket_upper)?;
    let (_, modulus_upper) = pole
        .modulus_interval()
        .ok_or(AmplitudeDecline::DominantModulusNotSimple)?;
    let below = count_roots_in(&bound.modulus_polynomial, &zero(), &modulus_upper)
        .ok_or(AmplitudeDecline::SturmDeclined)?;
    if below != 1 {
        return Err(AmplitudeDecline::DominantModulusNotSimple);
    }
    match minimal_modulus_is_simple(&factor, &modulus_upper) {
        None => return Err(AmplitudeDecline::ResultantDeclined),
        Some(false) => return Err(AmplitudeDecline::DominantModulusNotSimple),
        Some(true) => {}
    }

    let amplitude = compute_amplitude(
        &radius.reduced_numerator,
        &factor,
        &cofactor,
        multiplicity,
        &pole,
    )?;
    let tail = certify_tail(&radius, &bracket_upper)?;

    let tolerance = tolerance_cap();
    let samples = build_window(
        numerator,
        denominator,
        &pole,
        &amplitude,
        multiplicity - 1,
        base,
        &tolerance,
    )?;

    let certificate = AmplitudeCertificate {
        numerator: trim(numerator.to_vec()),
        denominator: trim(denominator.to_vec()),
        radius,
        dominant_factor: factor,
        multiplicity,
        cofactor,
        pole,
        amplitude,
        tail,
        samples,
        tolerance,
    };
    certificate
        .verify()
        .map_err(AmplitudeDecline::CertificateRefused)?;
    Ok(certificate)
}

#[cfg(test)]
mod tests {
    use super::{
        Amplitude, AmplitudeCertificate, AmplitudeDecline, AmplitudeError, AmplitudeSample,
        DominantPole, TailGap, WINDOW_LEN, amplitude_interval, compute_amplitude, div_exact,
        dominant_pole_amplitude, monic, one, radius_brackets, relative_error_bound, tolerance_cap,
        zero,
    };
    use crate::fps::FormalPowerSeries;
    use crate::fps_analytic::radius_of_convergence;
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use num_traits::Zero;

    fn int(value: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(value))
    }

    fn rat(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn poly(coefficients: &[i64]) -> Vec<BigRational> {
        coefficients.iter().map(|&c| int(c)).collect()
    }

    /// Produce a certificate, failing the test with the decline if it does not.
    fn certificate(numerator: &[i64], denominator: &[i64], base: usize) -> AmplitudeCertificate {
        match dominant_pole_amplitude(&poly(numerator), &poly(denominator), base) {
            Ok(certificate) => certificate,
            Err(reason) => panic!("expected a certificate, got {reason:?}"),
        }
    }

    fn decline(numerator: &[i64], denominator: &[i64], base: usize) -> AmplitudeDecline {
        match dominant_pole_amplitude(&poly(numerator), &poly(denominator), base) {
            Ok(certificate) => panic!("expected a decline, got {certificate:?}"),
            Err(reason) => reason,
        }
    }

    // -----------------------------------------------------------------------
    // What now certifies
    // -----------------------------------------------------------------------

    #[test]
    fn the_geometric_series_has_amplitude_exactly_one() {
        // 1/(1-2x) = sum 2^n x^n, so a(n) = 1 * n^0 * (1/2)^(-n) exactly and the
        // window's relative error is not merely small but zero.
        let certificate = certificate(&[1], &[1, -2], 8);
        assert_eq!(certificate.pole, DominantPole::Rational(rat(1, 2)));
        assert_eq!(certificate.multiplicity, 1);
        assert_eq!(certificate.exponent(), 0);
        assert_eq!(certificate.amplitude, Amplitude::Rational(one()));
        assert!(certificate.samples.iter().all(|s| s.error_bound.is_zero()));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn a_negative_dominant_pole_keeps_the_alternating_sign_in_the_pole_not_the_amplitude() {
        // 1/(1+2x) has a(n) = (-2)^n. The amplitude is +1 and the alternation
        // lives in zeta = -1/2, which is exactly why the certificate names a
        // signed pole rather than the radius.
        let certificate = certificate(&[1], &[1, 2], 8);
        assert_eq!(certificate.pole, DominantPole::Rational(rat(-1, 2)));
        assert_eq!(certificate.amplitude, Amplitude::Rational(one()));
        assert_eq!(certificate.samples[0].coefficient, int(256));
        assert_eq!(certificate.samples[1].coefficient, int(-512));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn a_double_pole_gives_growth_exponent_one_and_amplitude_one() {
        // 1/(1-2x)^2 has a(n) = (n+1)2^n, so C = 1 and k = 1; the relative error
        // is exactly 1/n, which is why a second-order pole needs a base in the
        // hundreds where a simple one converges geometrically.
        let certificate = certificate(&[1], &[1, -4, 4], 200);
        assert_eq!(certificate.multiplicity, 2);
        assert_eq!(certificate.exponent(), 1);
        assert_eq!(certificate.amplitude, Amplitude::Rational(one()));
        assert_eq!(certificate.samples[0].error_bound, rat(1, 200));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn a_triple_pole_gives_amplitude_one_half() {
        // 1/(1-2x)^3 has a(n) = binom(n+2,2) 2^n ~ (1/2) n^2 2^n, so C = 1/2 and
        // the exact relative error is (3n+2)/n^2.
        let certificate = certificate(&[1], &[1, -6, 12, -8], 400);
        assert_eq!(certificate.multiplicity, 3);
        assert_eq!(certificate.exponent(), 2);
        assert_eq!(certificate.amplitude, Amplitude::Rational(rat(1, 2)));
        assert_eq!(
            certificate.samples[0].error_bound,
            rat(3 * 400 + 2, 400 * 400)
        );
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn a_rescaled_pole_is_still_rational() {
        // 1/(2-3x): zeta = 2/3 and C = 1/2, so the amplitude is not forced to be
        // one by a normalization accident.
        let certificate = certificate(&[1], &[2, -3], 8);
        assert_eq!(certificate.pole, DominantPole::Rational(rat(2, 3)));
        assert_eq!(certificate.amplitude, Amplitude::Rational(rat(1, 2)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn fibonacci_amplitude_is_one_over_sqrt_five_as_an_exact_field_element() {
        // F(n) ~ phi^n / sqrt(5). The amplitude comes back as 1/5 + (2/5) zeta in
        // Q(zeta) with zeta^2 = 1 - zeta, and the independent check is that its
        // SQUARE is the rational 1/5 -- which pins it as 1/sqrt(5) without ever
        // computing a square root.
        let certificate = certificate(&[0, 1], &[1, -1, -1], 8);
        assert_eq!(certificate.dominant_factor, poly(&[-1, 1, 1]));
        assert_eq!(certificate.multiplicity, 1);
        let Amplitude::Algebraic { coefficients } = &certificate.amplitude else {
            panic!(
                "expected an algebraic amplitude, got {:?}",
                certificate.amplitude
            );
        };
        assert_eq!(coefficients, &vec![rat(1, 5), rat(2, 5)]);
        // (a + b z)^2 with z^2 = 1 - z is (a^2 + b^2) + (2ab - b^2) z.
        let (a, b) = (rat(1, 5), rat(2, 5));
        let constant = &a * &a + &b * &b;
        let linear = int(2) * &a * &b - &b * &b;
        assert_eq!(constant, rat(1, 5), "C^2's rational part is not 1/5");
        assert!(
            linear.is_zero(),
            "C^2 is not rational, so C is not 1/sqrt(5)"
        );
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn tribonacci_reaches_a_cubic_field_through_the_complex_rooted_route() {
        // 1/(1-x-x^2-x^3): the denominator is an irreducible cubic with one real
        // root and a conjugate pair of larger modulus, so no all-real-roots route
        // applies and the pairwise-product resultant is what decides both the
        // radius and the uniqueness of the dominant root.
        let certificate = certificate(&[1], &[1, -1, -1, -1], 8);
        assert_eq!(certificate.dominant_factor, poly(&[-1, 1, 1, 1]));
        let Amplitude::Algebraic { coefficients } = &certificate.amplitude else {
            panic!("expected an algebraic amplitude");
        };
        assert_eq!(coefficients, &vec![rat(5, 11), rat(5, 22), rat(3, 22)]);
        assert!(matches!(certificate.tail, TailGap::AtLeast(_)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn a_pole_with_no_other_singularity_is_recorded_as_such() {
        let certificate = certificate(&[1], &[1, -2], 8);
        assert!(
            matches!(certificate.tail, TailGap::OnlySingularity { .. }),
            "1/(1-2x) has one pole and nothing else; got {:?}",
            certificate.tail
        );
    }

    // -----------------------------------------------------------------------
    // What declines, and why
    // -----------------------------------------------------------------------

    #[test]
    fn two_dominant_factors_decline_rather_than_average() {
        // 1/(1-x^2) has poles at +1 and -1: a(n) alternates 1, 0, 1, 0, and no
        // single C n^k zeta^(-n) describes it.
        assert_eq!(
            decline(&[1], &[1, 0, -1], 8),
            AmplitudeDecline::SharedDominantModulus { factors: 2 }
        );
    }

    #[test]
    fn a_conjugate_dominant_pair_declines_with_the_periodicity_named() {
        // 1/(1+x^2) has coefficients 1, 0, -1, 0, ...: the dominant singularities
        // are +-i, non-real and of equal modulus.
        assert_eq!(
            decline(&[1], &[1, 0, 1], 8),
            AmplitudeDecline::DominantModulusNotSimple
        );
    }

    #[test]
    fn two_real_poles_of_equal_modulus_inside_one_irreducible_factor_decline() {
        // x^2 - 2 is irreducible with roots +-sqrt(2): one factor, two dominant
        // roots. This is the case the uniqueness test exists for, and it is not
        // caught by counting dominant FACTORS.
        assert_eq!(
            decline(&[1], &[-2, 0, 1], 8),
            AmplitudeDecline::DominantModulusNotSimple
        );
    }

    #[test]
    fn a_polynomial_has_no_dominant_pole() {
        assert_eq!(decline(&[1, 1], &[1], 8), AmplitudeDecline::RadiusNotUsable);
    }

    #[test]
    fn a_window_base_below_the_floor_declines() {
        assert_eq!(decline(&[1], &[1, -2], 3), AmplitudeDecline::SampleTooSmall);
    }

    #[test]
    fn a_base_too_small_for_the_subdominant_pole_declines_with_the_error_it_measured() {
        // 1/((1-2x)(1-3x)): a(n) = 3^(n+1) - 2^(n+1), so the relative error at
        // n = 8 is (2/3)^8 * (1/2)... = 512/19683, above the 1/100 tolerance. The
        // remedy is a larger base, and the decline says how far off it was.
        let reason = decline(&[1], &[1, -5, 6], 8);
        assert_eq!(
            reason,
            AmplitudeDecline::ToleranceExceeded {
                n: 8,
                error: rat(512, 19683)
            }
        );
        // ...and with a large enough base it certifies.
        let certificate = certificate(&[1], &[1, -5, 6], 16);
        assert_eq!(certificate.pole, DominantPole::Rational(rat(1, 3)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn a_window_whose_error_does_not_shrink_declines() {
        // (1+2x-5x^2)/((1-2x)(1-x^2)) has a(n) = 2^n + 1 - (-1)^n, so the relative
        // error is 0 at even n and 2^(1-n) at odd n. Starting the window at an
        // even index leaves the last sample above the first.
        assert_eq!(
            decline(&[1, 2, -5], &[1, -2, -1, 2], 8),
            AmplitudeDecline::ErrorDoesNotShrink
        );
        // The same function one index later shrinks and certifies.
        assert_eq!(
            certificate(&[1, 2, -5], &[1, -2, -1, 2], 9).verify(),
            Ok(())
        );
    }

    // -----------------------------------------------------------------------
    // Forged certificates: one per guard in `verify`
    // -----------------------------------------------------------------------

    #[test]
    fn forged_function_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.numerator = poly(&[2]);
        assert_eq!(certificate.verify(), Err(AmplitudeError::FunctionMismatch));
    }

    #[test]
    fn forged_zero_multiplicity_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.multiplicity = 0;
        assert_eq!(certificate.verify(), Err(AmplitudeError::ZeroMultiplicity));
    }

    #[test]
    fn forged_loose_tolerance_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.tolerance = rat(1, 2);
        assert_eq!(certificate.verify(), Err(AmplitudeError::ToleranceTooLoose));
    }

    #[test]
    fn forged_non_monic_dominant_factor_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.dominant_factor = poly(&[-1, 2]);
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::DominantFactorNotMonic)
        );
    }

    #[test]
    fn a_shared_dominant_modulus_is_refused_even_when_every_other_field_is_honest() {
        // Swap in 1/(1-x^2)'s radius certificate, which has TWO factors attaining
        // the radius. Nothing else about the certificate is touched.
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.numerator = poly(&[1]);
        certificate.denominator = poly(&[1, 0, -1]);
        certificate.radius = radius_of_convergence(&poly(&[1]), &poly(&[1, 0, -1])).unwrap();
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::SharedDominantModulus { factors: 2 })
        );
    }

    #[test]
    fn forged_multiplicity_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.multiplicity = 2;
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::DominantFactorMismatch)
        );
    }

    #[test]
    fn forged_cofactor_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.cofactor = vec![int(2) * &certificate.cofactor[0]];
        assert!(
            matches!(
                certificate.verify(),
                Err(AmplitudeError::CofactorMismatch { .. })
            ),
            "a doubled cofactor was accepted"
        );
    }

    #[test]
    fn a_pole_that_is_not_a_root_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.pole = DominantPole::Rational(rat(1, 3));
        assert_eq!(certificate.verify(), Err(AmplitudeError::PoleNotARoot));
    }

    #[test]
    fn a_pole_bracket_holding_two_roots_is_refused() {
        // 1 - 3x + x^2 is irreducible with both roots real and positive,
        // (3 +- sqrt 5)/2 ~ 0.382 and 2.618. A bracket spanning both is not an
        // isolation, and the count says so.
        let mut certificate = certificate(&[1], &[1, -3, 1], 8);
        let DominantPole::Algebraic {
            minimal_polynomial, ..
        } = certificate.pole.clone()
        else {
            panic!("expected an algebraic pole");
        };
        certificate.pole = DominantPole::Algebraic {
            minimal_polynomial,
            lower: rat(3, 10),
            upper: int(3),
        };
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::PoleNotIsolated {
                expected: 1,
                found: 2
            })
        );
    }

    #[test]
    fn a_degenerate_pole_bracket_is_refused() {
        // `lower >= upper` is not a bracket at all. Without the guard the Sturm
        // count over the empty interval is zero and the refusal changes shape,
        // which is what makes the guard's deletion visible.
        let mut certificate = certificate(&[0, 1], &[1, -1, -1], 8);
        let DominantPole::Algebraic {
            minimal_polynomial, ..
        } = certificate.pole.clone()
        else {
            panic!("expected an algebraic pole");
        };
        certificate.pole = DominantPole::Algebraic {
            minimal_polynomial,
            lower: rat(3, 5),
            upper: rat(3, 5),
        };
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::MalformedPoleBracket)
        );
    }

    #[test]
    fn a_pole_bracket_straddling_the_origin_is_refused() {
        let mut certificate = certificate(&[0, 1], &[1, -1, -1], 8);
        let DominantPole::Algebraic {
            minimal_polynomial, ..
        } = certificate.pole.clone()
        else {
            panic!("expected an algebraic pole");
        };
        certificate.pole = DominantPole::Algebraic {
            minimal_polynomial,
            lower: int(-2),
            upper: int(1),
        };
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::MalformedPoleBracket)
        );
    }

    #[test]
    fn the_subdominant_root_of_the_same_factor_is_refused_as_the_pole() {
        // Fibonacci's other root, -1.618, is a perfectly good root of the same
        // irreducible factor -- and is not the dominant singularity.
        let mut certificate = certificate(&[0, 1], &[1, -1, -1], 8);
        let DominantPole::Algebraic {
            minimal_polynomial, ..
        } = certificate.pole.clone()
        else {
            panic!("expected an algebraic pole");
        };
        certificate.pole = DominantPole::Algebraic {
            minimal_polynomial,
            lower: int(-2),
            upper: rat(-3, 2),
        };
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::PoleModulusMismatch)
        );
    }

    #[test]
    fn a_forged_minimal_polynomial_is_refused() {
        let mut certificate = certificate(&[0, 1], &[1, -1, -1], 8);
        let DominantPole::Algebraic { lower, upper, .. } = certificate.pole.clone() else {
            panic!("expected an algebraic pole");
        };
        certificate.pole = DominantPole::Algebraic {
            minimal_polynomial: poly(&[-1, 0, 1]),
            lower,
            upper,
        };
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::MinimalPolynomialMismatch)
        );
    }

    #[test]
    fn two_roots_sharing_the_minimal_modulus_are_refused_by_the_simplicity_test() {
        // The producer declines on 1/(x^2-2), so the certificate is assembled by
        // hand from its own radius certificate: everything below the simplicity
        // test is honest, and only that test can refuse it. `verify` returns at
        // the pole step, so the window is left empty deliberately.
        let numerator = poly(&[1]);
        let denominator = poly(&[-2, 0, 1]);
        let radius = radius_of_convergence(&numerator, &denominator).unwrap();
        let factor = monic(&radius.factors[0].factor);
        let cofactor = div_exact(&radius.reduced_denominator, &factor).unwrap();
        let (lower, upper, _) = radius_brackets(&radius.radius).unwrap();
        let certificate = AmplitudeCertificate {
            numerator,
            denominator,
            radius,
            dominant_factor: factor.clone(),
            multiplicity: 1,
            cofactor,
            pole: DominantPole::Algebraic {
                minimal_polynomial: factor,
                lower,
                upper,
            },
            amplitude: Amplitude::Rational(one()),
            tail: TailGap::AtLeast(int(100)),
            samples: Vec::new(),
            tolerance: tolerance_cap(),
        };
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::DominantModulusNotSimple)
        );
    }

    #[test]
    fn a_forged_rational_amplitude_is_caught_by_the_partial_fraction_cross_check() {
        // The cross-check runs BEFORE the residue recomputation precisely so that
        // both guards are reachable: this one dies if the cross-check is removed.
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.amplitude = Amplitude::Rational(int(2));
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::PartialFractionDisagrees)
        );
    }

    #[test]
    fn a_forged_algebraic_amplitude_is_caught_by_the_residue_recomputation() {
        // The partial-fraction route cannot express an algebraic pole, so it
        // steps aside and the residue recomputation is what refuses this.
        let mut certificate = certificate(&[0, 1], &[1, -1, -1], 8);
        certificate.amplitude = Amplitude::Algebraic {
            coefficients: vec![rat(1, 5), rat(3, 5)],
        };
        assert_eq!(certificate.verify(), Err(AmplitudeError::AmplitudeMismatch));
    }

    #[test]
    fn an_amplitude_of_the_wrong_shape_is_refused() {
        let mut certificate = certificate(&[0, 1], &[1, -1, -1], 8);
        certificate.amplitude = Amplitude::Rational(one());
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::AmplitudeShapeMismatch)
        );
    }

    #[test]
    fn a_tail_bound_below_the_radius_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.tail = TailGap::AtLeast(rat(1, 4));
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::TailBoundNotAboveRadius)
        );
    }

    #[test]
    fn a_tail_bound_that_swallows_the_next_singularity_is_refused() {
        // 1/((1-2x)(1-3x)) has its second pole at 1/2. Claiming a gap out to 1
        // asserts there is nothing there, and there is.
        let mut certificate = certificate(&[1], &[1, -5, 6], 16);
        certificate.tail = TailGap::AtLeast(one());
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::TailBoundNotCertified { found: 1 })
        );
    }

    #[test]
    fn a_window_of_the_wrong_length_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.samples.truncate(WINDOW_LEN - 1);
        assert_eq!(certificate.verify(), Err(AmplitudeError::MalformedWindow));
    }

    #[test]
    fn a_window_starting_below_the_floor_is_refused() {
        // Indices 4..7 are consecutive and their coefficients and error bounds are
        // recomputed honestly -- the only thing wrong with them is that they are
        // too early to be evidence.
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.samples = rebuilt_window(&certificate, 4);
        assert_eq!(certificate.verify(), Err(AmplitudeError::MalformedWindow));
    }

    #[test]
    fn a_window_with_a_gap_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        let last = certificate.samples.len() - 1;
        certificate.samples[last] = AmplitudeSample {
            index: 12,
            coefficient: int(4096),
            error_bound: zero(),
        };
        assert_eq!(certificate.verify(), Err(AmplitudeError::MalformedWindow));
    }

    #[test]
    fn a_forged_coefficient_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.samples[1].coefficient = int(513);
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::CoefficientMismatch { index: 1 })
        );
    }

    #[test]
    fn a_forged_error_bound_is_refused() {
        let mut certificate = certificate(&[1], &[1, -2], 8);
        certificate.samples[1].error_bound = rat(1, 1000);
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::ErrorBoundMismatch { index: 1 })
        );
    }

    #[test]
    fn a_tolerance_the_window_does_not_meet_is_refused() {
        // The double pole's error is exactly 1/200 at n = 200; a tolerance of
        // 1/10^9 is inside the cap and outside what the window achieves.
        let mut certificate = certificate(&[1], &[1, -4, 4], 200);
        certificate.tolerance = rat(1, 1_000_000_000);
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::ToleranceExceeded { index: 0 })
        );
    }

    #[test]
    fn a_window_whose_error_grows_is_refused() {
        // Rebuild the honest window of the alternating-remainder function one
        // index earlier, where the error runs 0, 2^-8, 0, 2^-10: every sample is
        // inside the tolerance and every value recomputes, and the only thing
        // wrong is that the last exceeds the first.
        let mut certificate = certificate(&[1, 2, -5], &[1, -2, -1, 2], 9);
        certificate.samples = rebuilt_window(&certificate, 8);
        assert!(
            certificate.samples[0].error_bound < certificate.samples[WINDOW_LEN - 1].error_bound,
            "the fixture does not exhibit a growing error"
        );
        assert_eq!(
            certificate.verify(),
            Err(AmplitudeError::ErrorDoesNotShrink)
        );
    }

    /// The certificate's own window recomputed at a different base, using the
    /// same helpers `verify` uses — so every value in it is honest.
    fn rebuilt_window(certificate: &AmplitudeCertificate, base: usize) -> Vec<AmplitudeSample> {
        let order = base + WINDOW_LEN - 1;
        let (series, _) = FormalPowerSeries::from_rational_function(
            &certificate.numerator,
            &certificate.denominator,
            order,
        )
        .expect("the expansion is available at this order");
        let pole = certificate.pole.interval().expect("a well-formed pole");
        let amplitude = amplitude_interval(&certificate.amplitude, &pole);
        (0..WINDOW_LEN)
            .map(|offset| {
                let index = base + offset;
                let coefficient = series
                    .coefficient(index)
                    .expect("the expansion reaches this index")
                    .clone();
                let error_bound = relative_error_bound(
                    &coefficient,
                    &pole,
                    &amplitude,
                    index,
                    certificate.exponent(),
                )
                .expect("a nonzero amplitude");
                AmplitudeSample {
                    index,
                    coefficient,
                    error_bound,
                }
            })
            .collect()
    }

    // -----------------------------------------------------------------------
    // The producer's own decisions, exercised directly
    // -----------------------------------------------------------------------

    #[test]
    fn the_residue_formula_agrees_with_the_partial_fraction_leading_coefficient() {
        // Not a forgery: a positive cross-check that the two routes to C agree on
        // every shape the machine-width partial-fraction route reaches.
        for (numerator, denominator, base) in [
            (vec![1_i64], vec![1_i64, -2], 8usize),
            (vec![1], vec![2, -3], 8),
            (vec![1], vec![1, 2], 8),
            (vec![1, 1], vec![1, -2], 8),
            (vec![1], vec![1, -5, 6], 16),
        ] {
            let certificate = certificate(&numerator, &denominator, base);
            assert_eq!(
                certificate.verify(),
                Ok(()),
                "{numerator:?}/{denominator:?} did not verify"
            );
        }
    }

    #[test]
    fn compute_amplitude_reproduces_the_certificate_it_is_asked_about() {
        let certificate = certificate(&[0, 1], &[1, -1, -1], 8);
        let recomputed = compute_amplitude(
            &certificate.radius.reduced_numerator,
            &certificate.dominant_factor,
            &certificate.cofactor,
            certificate.multiplicity,
            &certificate.pole,
        )
        .expect("the residue formula has a value here");
        assert_eq!(recomputed, certificate.amplitude);
    }
}
