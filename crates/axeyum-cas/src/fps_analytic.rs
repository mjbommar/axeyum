//! Radius of convergence and coefficient asymptotics for **rational** power
//! series — the analytic companion to [`crate::fps`].
//!
//! # Why this is not just `1/max|root|`
//!
//! The first slice of the power-series work refused to ship a radius because
//! the honest answer for `p/q` is `1/max|root of q|` over the **complex** roots
//! and the crate's Sturm machinery certifies *real* roots only. Shipping the
//! real-root answer would have been wrong on `1/(1+x²)`, whose denominator has
//! no real root at all.
//!
//! The route here avoids the complex plane entirely by working with **moduli**
//! rather than roots. Factor `q` over ℚ; for each factor `f` decide the minimal
//! modulus of its roots by one of four routes:
//!
//! | route | applies when | the minimal modulus is |
//! |---|---|---|
//! | [`ModulusRoute::AllRealRoots`] | `f` has `deg f` distinct real roots (Sturm) | the smallest positive root of `g(t) = f(t)·f(−t)` |
//! | [`ModulusRoute::ConjugatePair`] | `deg f = 2` with negative discriminant | `√(c/a)`, the root of `g(t) = t² − c/a` |
//! | [`ModulusRoute::PairwiseResultant`] | any `f` with `f(0) ≠ 0` and `deg f ≤ 4` | the smallest positive root of `s(t²)`, `s` the square-free part of `Res_z(f(z), z^n f(t/z))` |
//! | [`ModulusRoute::ReciprocalCauchy`] | `deg f > 4` | unknown; only the bound `1/(1 + maxᵢ≥₁|aᵢ/a₀|)` |
//!
//! The first three are **exact**: `g`'s positive real roots contain the moduli
//! of `f`'s roots and its *smallest* positive real root is the smallest of them,
//! so the radius of the whole function is the smallest positive root of
//! `G = Π g`, isolated by a Sturm count. The fourth certifies a **lower bound**
//! on the radius and nothing more.
//!
//! The first two are kept because they are far cheaper, not because the third
//! misses anything they catch: [`ModulusRoute::PairwiseResultant`] applies to
//! every factor the other two do. The routes are tried cheapest first.
//!
//! # The theorem behind the pairwise-product route
//!
//! > **Theorem.** Let `f ∈ ℝ[z]` have degree `n ≥ 1`, leading coefficient `aₙ`,
//! > constant term `a₀ ≠ 0`, and complex roots `r₁, …, rₙ` with multiplicity.
//! > Put
//! >
//! > ```text
//! > g(t) = Res_z( f(z), zⁿ·f(t/z) ).
//! > ```
//! >
//! > Then `g(t) = aₙ^{2n} · Π_{i,j} (t − rᵢrⱼ)`, it has degree `n²`, `g(0) ≠ 0`,
//! > and **its smallest positive real root is `minᵢ |rᵢ|²`.**
//!
//! *Proof.* Write `h_t(z) = zⁿ f(t/z) = Σₖ aₖ tᵏ z^{n−k}`. Its leading
//! coefficient in `z` is `a₀ ≠ 0`, so `deg_z h_t = n` and the resultant is the
//! determinant of a `2n × 2n` Sylvester matrix. Evaluating `h_t` at a root of
//! `f`,
//!
//! ```text
//! h_t(rᵢ) = rᵢⁿ · f(t/rᵢ) = rᵢⁿ · aₙ Πⱼ (t/rᵢ − rⱼ) = aₙ Πⱼ (t − rᵢ rⱼ),
//! ```
//!
//! and `Res_z(f, h_t) = aₙ^{deg h} Πᵢ h_t(rᵢ)` gives the product form. Since no
//! `rᵢ` is zero, `g(0) = (−1)ⁿ a₀^{2n} ≠ 0`.
//!
//! Now let `m = minᵢ |rᵢ| > 0`. Two halves:
//!
//! 1. **No root of `g` has modulus below `m²`.** Every root is some `rᵢ rⱼ`, and
//!    `|rᵢ rⱼ| = |rᵢ|·|rⱼ| ≥ m·m`. A *positive real* root `t` is its own
//!    modulus, so `t ≥ m²`.
//! 2. **`m²` is a root of `g`.** This is where `f` being **real** is used: its
//!    roots are closed under conjugation, so for an index `i` attaining `m`
//!    there is a `j` with `rⱼ = r̄ᵢ` (`j = i` when `rᵢ` is real), and
//!    `rᵢ rⱼ = rᵢ r̄ᵢ = |rᵢ|² = m²`, which is positive and real.
//!
//! Together, `m²` is a positive real root and none is smaller. ∎
//!
//! Two consequences worth stating because they are what make the certificate
//! small and the checking cheap:
//!
//! - **Spurious products need no filtering.** `g` does have positive real roots
//!   that are not moduli — `f = (z−1)(z−4)` gives the root `4 = 1·4` where the
//!   moduli squared are `1` and `16`. Part 1 of the proof says such a root can
//!   only sit *above* `m²`, never below it, so taking the smallest positive root
//!   is already correct. The certificate therefore records no rejected roots and
//!   no per-root resultant evaluations: there is nothing to reject.
//!   `a_spurious_pairwise_product_is_never_the_smallest_positive_root` pins that
//!   example, and `forged_spurious_pairwise_product_claimed_as_the_radius_is_refused`
//!   pins that *claiming* the spurious root is caught by the Sturm count.
//! - **The square-free part is taken before the substitution.** The root *set*
//!   is what the theorem is about, so dropping multiplicity is free — and it is
//!   not cosmetic: for `Φ₅` it takes `g = (t−1)⁴·Φ₅(t)³` of degree 16 down to
//!   `t⁵ − 1`, so the Sturm chain runs at degree 10 rather than 32.
//!
//! Finally, `s(t²)` for the square-free `s` turns the squared moduli back into
//! moduli: `t ↦ t²` is an order isomorphism of the positive reals, so the
//! smallest positive root of `s(t²)` is `√(m²) = m`.
//!
//! ## What the certificate makes falsifiable
//!
//! [`FactorModulusBound::verify`] re-derives the resultant from the factor's own
//! coefficients — it rebuilds the Sylvester matrix, recomputes the determinant,
//! retakes the square-free part, resubstitutes, and compares — and then re-runs
//! the Sturm count that the lower bound rests on.
//!
//! The determinant itself comes from `axeyum_ir::poly_big::big_determinant`
//! (exact evaluation–interpolation over `BigRational`). Because a re-derivation
//! that reuses the same primitive cannot catch that primitive being wrong, the
//! producer *and* the verifier both check two exact consequences of the product
//! form that are not how the determinant is computed:
//!
//! - `deg g = n²`;
//! - the monic `g` has `g(0) = Πᵢⱼ(−rᵢrⱼ) = (−1)ⁿ (a₀/aₙ)^{2n}`, using
//!   `Πᵢ rᵢ = (−1)ⁿ a₀/aₙ`.
//!
//! A mismatch **declines** rather than answering. Both checks live in
//! `accept_pairwise_resultant`, which takes the determinant as an argument
//! precisely so a test can hand it a corrupted one — a guard whose only input is
//! a value no test can perturb is a guard no test can kill.
//!
//! ## When the lower-bound label still appears
//!
//! Only above `MAX_RESULTANT_FACTOR_DEGREE`. The modulus polynomial has degree
//! `2n²` in the factor's degree, and the Sturm chain that isolates its smallest
//! positive root costs superlinearly in that; the cap is a **cost** policy, not
//! a mathematical boundary. So `Φ₅` (degree 4) is now exactly 1 and `Φ₇`
//! (degree 6) keeps the bound `1/2`, and the reason recorded is the degree.
//!
//! The route also declines — never answers wrongly — when the determinant fails
//! either self-check above, or when the reused factorizer cannot take the
//! denominator to ℚ-factors at all.
//!
//! # What carries what label
//!
//! - [`radius_of_convergence`] is **certified**: an
//!   [`RadiusOfConvergence::Exact`] or [`RadiusOfConvergence::Algebraic`] value
//!   is the radius, and a [`RadiusOfConvergence::LowerBound`] is a proved lower
//!   bound on it. Both are re-derived by `verify`.
//! - [`coefficient_asymptotics`] is **`asymptotic-verified-at-finite-n`**, never
//!   *certified*. See its documentation for exactly what is and is not claimed.
//!
//! # What is still out of reach
//!
//! - **Denominator factors above `MAX_RESULTANT_FACTOR_DEGREE`.** A cost cap,
//!   not a gap in the mathematics: the theorem applies at every degree, and
//!   raising the cap is a measurement question about the Sturm chain at degree
//!   `2n²`.
//! - **Transcendental singularities.** Everything here is about a *rational*
//!   generating function, whose singularities are poles at the denominator's
//!   zeros. `1/(1 − eˣ)`, `Γ`-type growth, and any series whose nearest
//!   singularity is a branch point or an essential one are outside the whole
//!   construction — there is no denominator to factor.
//! - **Multivariate series.** `crate::fps` is univariate, so a diagonal or a
//!   bivariate generating function has no radius here at all; the analogue is a
//!   domain of convergence, and the modulus construction does not lift to it
//!   unchanged.
//! - **An exact constant `C`.** The radius is pinned exactly; the amplitude in
//!   `a(n) ≈ C·nᵏ·ρ⁻ⁿ` is still only sampled, and
//!   [`CoefficientAsymptotics`] is labelled accordingly.
//!
//! # Reuse
//!
//! `crate::factor_int::factor_univariate_over_q` factors the denominator;
//! [`crate::sturm::count_real_roots_in`] / [`crate::sturm::isolate_real_roots`]
//! answer every root count they can hold; and
//! `axeyum_ir::poly_big::big_determinant` computes the Sylvester determinant
//! behind [`ModulusRoute::PairwiseResultant`] by exact
//! evaluation–interpolation over [`BigRational`].
//!
//! The Sylvester *matrix* is the one thing rebuilt rather than reused: the
//! `axeyum-ir` builder for the machine width takes `i128` coefficients and the
//! `BigRational` one is private to that crate, so the ten lines are restated
//! here in the same convention.
//!
//! There is also a second Sturm width. `crate::sturm` works over the
//! machine-width `axeyum_ir::Rational` and declines rather than guessing when a
//! coefficient leaves `i128` — which the degree-`2n²` modulus polynomials of the
//! new route do on the second or third remainder of the chain. `RootCounter`
//! therefore tries that reuse first and falls back to a Sturm chain over
//! [`BigRational`], with every member positive-scaled to a primitive integer
//! polynomial so the coefficients do not double at each Euclidean step. The two
//! widths are held to agree by `bignum_and_machine_sturm_counts_agree` over the
//! polynomials both can take.
//!
//! The polynomial arithmetic below is over [`BigRational`] because `crate::fps`
//! is, and because every modulus polynomial squares the coefficient size before
//! Sturm ever sees it.

use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::fps::{CertificateError as SeriesError, FormalPowerSeries};

/// Bits of bisection used to refine an irrational radius past its Sturm-certified
/// bracket. The refinement is by sign change on the square-free part, so it costs
/// only exact rational evaluation and never a deeper Sturm chain.
const REFINEMENT_BITS: u32 = 96;

/// The largest factor degree [`ModulusRoute::PairwiseResultant`] will attempt.
///
/// The route's modulus polynomial has degree `2n²` in the factor's degree `n`,
/// and the Sturm chain that isolates its smallest positive root costs
/// superlinearly in that. At `n = 4` the polynomial has degree 32 before the
/// square-free reduction and the whole radius lands well inside a second; at
/// `n = 6` it is degree 72 and the chain dominates the crate's test sweep.
/// Above the cap the factor keeps the [`ModulusRoute::ReciprocalCauchy`]
/// lower-bound label, with that as the stated reason.
const MAX_RESULTANT_FACTOR_DEGREE: usize = 4;

/// The largest relative error [`CoefficientAsymptotics::verify`] will accept at
/// the coarsest sample. A certificate stating a looser tolerance is refused, so
/// a forger cannot buy acceptance by widening the claim.
fn tolerance_cap() -> BigRational {
    BigRational::new(BigInt::from(1), BigInt::from(100))
}

/// The largest relative error a [`CoefficientAsymptotics`] certificate may state
/// at its coarsest sample, and the tolerance [`coefficient_asymptotics`] holds
/// itself to.
///
/// `verify` refuses a certificate stating anything looser, so widening the claim
/// buys a forger nothing.
pub fn asymptotic_tolerance() -> BigRational {
    tolerance_cap()
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Why a certificate in this module was refused.
///
/// Each variant names one independently reachable guard, so a refusal says
/// *which* re-derivation disagreed rather than merely that one did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnalyticError {
    /// The denominator is empty or identically zero.
    EmptyDenominator,
    /// `q(0) = 0`, so `p/q` is not a power series at the origin.
    DenominatorVanishesAtZero,
    /// `common_factor · reduced_numerator` does not reproduce the numerator.
    NumeratorSplitMismatch {
        /// The lowest degree at which the product disagrees.
        degree: usize,
    },
    /// `common_factor · reduced_denominator` does not reproduce the denominator.
    DenominatorSplitMismatch {
        /// The lowest degree at which the product disagrees.
        degree: usize,
    },
    /// The carried Bézout pair does not witness `gcd(p_red, q_red) = 1`, so a
    /// singularity of `q_red` might be cancelled by `p_red` and the claimed
    /// radius could be too small.
    NotCoprime,
    /// `content · Π factorⁱ` does not reproduce the reduced denominator.
    FactorProductMismatch {
        /// The lowest degree at which the product disagrees.
        degree: usize,
    },
    /// The factorization's leading content is zero.
    ZeroContent,
    /// A factor vanishes at the origin, so it contributes a zero root and the
    /// modulus route does not apply.
    FactorVanishesAtZero {
        /// Index of the offending factor.
        factor: usize,
    },
    /// A factor is constant, so it names no root.
    FactorIsConstant {
        /// Index of the offending factor.
        factor: usize,
    },
    /// The declared route's precondition fails for this factor: not every root
    /// is real, or the degree/discriminant shape does not hold.
    RouteNotApplicable {
        /// Index of the offending factor.
        factor: usize,
    },
    /// The factor's carried modulus polynomial is not the one its route defines.
    ModulusPolynomialMismatch {
        /// Index of the offending factor.
        factor: usize,
    },
    /// The factor's claimed lower bound on `|root|` is not certified by its
    /// route: a root of smaller modulus is not excluded.
    LowerBoundNotCertified {
        /// Index of the offending factor.
        factor: usize,
    },
    /// A claimed lower bound is zero or negative, so it says nothing.
    NonPositiveBound,
    /// The global lower bound exceeds a factor's own certified lower bound.
    LowerBoundExceedsFactor {
        /// Index of the factor that refutes it.
        factor: usize,
    },
    /// An exact radius was claimed while some factor is only bound-certified.
    InexactRoute {
        /// Index of the bound-only factor.
        factor: usize,
    },
    /// The carried global modulus polynomial is not the product of the factors'.
    GlobalModulusMismatch,
    /// The global modulus polynomial vanishes at the origin, which would make a
    /// "smallest positive root" claim meaningless.
    ModulusVanishesAtZero,
    /// A bracket is malformed: not `0 < lower ≤ upper`, or the refined bracket
    /// escapes the Sturm-certified one.
    MalformedBracket,
    /// A value claimed to be a root of the modulus polynomial is not one.
    NotARoot,
    /// The Sturm count over the interval disagrees with the claim.
    RootCountMismatch {
        /// The count the claim needs.
        expected: usize,
        /// The count Sturm reports.
        found: usize,
    },
    /// The refined bracket carries no sign change, so it does not trap the root.
    NoSignChange,
    /// A reused root count declined — a coefficient outside `i128`, or one of
    /// the Sturm machinery's own caps. Not a refutation.
    SturmDeclined,
    /// The pairwise-product resultant could not be re-derived for this factor:
    /// the determinant came back at the wrong degree, or failed the
    /// constant-term identity `g(0) = (−1)ⁿ (a₀/aₙ)^{2n}` that pins it. Not a
    /// refutation of the radius — a refusal to trust the primitive that
    /// produced it.
    ResultantDeclined {
        /// Index of the offending factor.
        factor: usize,
    },
    /// The asymptotics certificate names a different function than its radius
    /// certificate does.
    FunctionMismatch,
    /// The asymptotics certificate rests on a radius that is only bounded.
    RadiusNotExact,
    /// The rational stand-in `ρ̃` lies outside the radius's certified bracket.
    RhoOutsideBracket,
    /// The sample indices are not `N, 2N, 4N` with `N` large enough.
    MalformedSamples,
    /// A recomputed coefficient disagrees with the carried one.
    CoefficientMismatch {
        /// Which of the three samples.
        index: usize,
    },
    /// A sampled coefficient is zero, so its normalized ratio is undefined.
    ZeroCoefficient {
        /// Which of the three samples.
        index: usize,
    },
    /// A recomputed normalized ratio disagrees with the carried one.
    RatioMismatch {
        /// Which of the three samples.
        index: usize,
    },
    /// A recomputed relative error disagrees with the carried one.
    RelativeErrorMismatch {
        /// Which of the three samples.
        index: usize,
    },
    /// The relative errors do not decrease along the three samples.
    ErrorsDoNotShrink {
        /// The sample at which the sequence stops decreasing.
        index: usize,
    },
    /// The coarsest sample's relative error exceeds the stated tolerance.
    ToleranceExceeded,
    /// The stated tolerance is wider than this module will accept.
    ToleranceTooLoose,
    /// The declared polynomial-growth exponent is not the one the dominant
    /// factors' multiplicities give.
    ExponentMismatch {
        /// The exponent the certificate declares.
        declared: u32,
        /// The exponent re-derived from the factorization.
        derived: u32,
    },
    /// No factor's modulus polynomial has the radius as a root, so the
    /// asymptotic form has no dominant singularity to rest on.
    NoDominantFactor,
    /// The reused series expansion refused its own certificate.
    SeriesCertificate(SeriesError),
    /// The reused series expansion declined outright.
    SeriesDeclined,
}

impl core::fmt::Display for AnalyticError {
    // A flat dispatch: one arm per guard, which is the point -- a refusal names
    // the re-derivation that disagreed.
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AnalyticError::EmptyDenominator => write!(f, "empty denominator"),
            AnalyticError::DenominatorVanishesAtZero => {
                write!(f, "the denominator vanishes at the origin")
            }
            AnalyticError::NumeratorSplitMismatch { degree } => {
                write!(f, "numerator split fails at degree {degree}")
            }
            AnalyticError::DenominatorSplitMismatch { degree } => {
                write!(f, "denominator split fails at degree {degree}")
            }
            AnalyticError::NotCoprime => {
                write!(f, "the Bézout pair does not witness coprimality")
            }
            AnalyticError::FactorProductMismatch { degree } => {
                write!(f, "the factorization fails at degree {degree}")
            }
            AnalyticError::ZeroContent => write!(f, "zero factorization content"),
            AnalyticError::FactorVanishesAtZero { factor } => {
                write!(f, "factor {factor} vanishes at the origin")
            }
            AnalyticError::FactorIsConstant { factor } => {
                write!(f, "factor {factor} is constant")
            }
            AnalyticError::RouteNotApplicable { factor } => {
                write!(
                    f,
                    "the declared modulus route does not apply to factor {factor}"
                )
            }
            AnalyticError::ModulusPolynomialMismatch { factor } => {
                write!(f, "factor {factor} carries the wrong modulus polynomial")
            }
            AnalyticError::LowerBoundNotCertified { factor } => {
                write!(f, "factor {factor}'s lower bound is not certified")
            }
            AnalyticError::NonPositiveBound => write!(f, "a claimed bound is not positive"),
            AnalyticError::LowerBoundExceedsFactor { factor } => {
                write!(f, "the global lower bound exceeds factor {factor}'s own")
            }
            AnalyticError::InexactRoute { factor } => {
                write!(
                    f,
                    "an exact radius was claimed but factor {factor} is bound-only"
                )
            }
            AnalyticError::GlobalModulusMismatch => {
                write!(
                    f,
                    "the global modulus polynomial is not the factors' product"
                )
            }
            AnalyticError::ModulusVanishesAtZero => {
                write!(f, "the modulus polynomial vanishes at the origin")
            }
            AnalyticError::MalformedBracket => write!(f, "malformed bracket"),
            AnalyticError::NotARoot => write!(f, "the claimed exact radius is not a root"),
            AnalyticError::RootCountMismatch { expected, found } => {
                write!(
                    f,
                    "Sturm counts {found} roots where the claim needs {expected}"
                )
            }
            AnalyticError::NoSignChange => write!(f, "the refined bracket has no sign change"),
            AnalyticError::SturmDeclined => write!(f, "the reused root count declined"),
            AnalyticError::ResultantDeclined { factor } => write!(
                f,
                "the pairwise-product resultant of factor {factor} did not re-derive"
            ),
            AnalyticError::FunctionMismatch => {
                write!(f, "the radius certificate describes a different function")
            }
            AnalyticError::RadiusNotExact => write!(f, "the radius is only bounded, not exact"),
            AnalyticError::RhoOutsideBracket => {
                write!(
                    f,
                    "the rational stand-in for the radius is outside its bracket"
                )
            }
            AnalyticError::MalformedSamples => write!(f, "malformed sample indices"),
            AnalyticError::CoefficientMismatch { index } => {
                write!(f, "sample {index} carries the wrong coefficient")
            }
            AnalyticError::ZeroCoefficient { index } => {
                write!(f, "sample {index} has a zero coefficient")
            }
            AnalyticError::RatioMismatch { index } => {
                write!(f, "sample {index} carries the wrong normalized ratio")
            }
            AnalyticError::RelativeErrorMismatch { index } => {
                write!(f, "sample {index} carries the wrong relative error")
            }
            AnalyticError::ErrorsDoNotShrink { index } => {
                write!(f, "the relative error does not shrink at sample {index}")
            }
            AnalyticError::ToleranceExceeded => {
                write!(f, "the relative error exceeds the tolerance")
            }
            AnalyticError::ToleranceTooLoose => write!(f, "the stated tolerance is too loose"),
            AnalyticError::ExponentMismatch { declared, derived } => {
                write!(
                    f,
                    "declared growth exponent {declared} but the factorization gives {derived}"
                )
            }
            AnalyticError::NoDominantFactor => write!(f, "no factor attains the radius"),
            AnalyticError::SeriesCertificate(inner) => write!(f, "series certificate: {inner}"),
            AnalyticError::SeriesDeclined => write!(f, "the series expansion declined"),
        }
    }
}

impl core::error::Error for AnalyticError {}

/// Why a producer in this module declined to answer.
///
/// A decline is never a refutation: it says the route did not reach an answer,
/// and names which step gave up.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnalyticDecline {
    /// The denominator is empty or identically zero.
    EmptyDenominator,
    /// `q(0) = 0`: the expansion is not a power series at the origin.
    SingularAtZero,
    /// The reused factorizer declined (coefficients outside `i128`, or its own
    /// degree cap).
    FactorizationDeclined,
    /// A reused Sturm root count declined.
    SturmDeclined,
    /// Isolating the smallest positive root of the modulus polynomial did not
    /// converge within the iteration cap.
    IsolationDeclined,
    /// The producer built a certificate its own checker refused. This is a bug
    /// report, not an answer.
    CertificateRefused(AnalyticError),
    /// Coefficient asymptotics need an exact radius; this one is bound-only.
    RadiusNotExact,
    /// A sampled coefficient vanished, so the normalized ratio is undefined.
    /// Rational functions with several dominant singularities — `1/(1+x²)`, say
    /// — oscillate and land here.
    ZeroCoefficient {
        /// Which of the three samples.
        index: usize,
    },
    /// The sampled relative errors did not decrease, so the sampled evidence
    /// does not support the asymptotic form.
    ErrorsDoNotShrink,
    /// The coarsest sample's relative error is above
    /// [`asymptotic_tolerance`]. Increase the base sample index and try again.
    ToleranceExceeded {
        /// The relative error measured at the coarsest sample.
        error: BigRational,
    },
    /// The base sample index is too small for three separated samples.
    SampleTooSmall,
    /// The reused series expansion declined.
    SeriesDeclined,
    /// No factor of the denominator attains the radius.
    NoDominantFactor,
}

impl core::fmt::Display for AnalyticDecline {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AnalyticDecline::EmptyDenominator => write!(f, "empty denominator"),
            AnalyticDecline::SingularAtZero => write!(f, "the denominator vanishes at the origin"),
            AnalyticDecline::FactorizationDeclined => write!(f, "the factorizer declined"),
            AnalyticDecline::SturmDeclined => write!(f, "a Sturm root count declined"),
            AnalyticDecline::IsolationDeclined => write!(f, "root isolation did not converge"),
            AnalyticDecline::CertificateRefused(inner) => {
                write!(f, "the producer's own checker refused: {inner}")
            }
            AnalyticDecline::RadiusNotExact => write!(f, "the radius is only bounded"),
            AnalyticDecline::ZeroCoefficient { index } => {
                write!(f, "the coefficient at sample {index} is zero")
            }
            AnalyticDecline::ErrorsDoNotShrink => write!(f, "the sampled errors do not shrink"),
            AnalyticDecline::ToleranceExceeded { error } => {
                write!(
                    f,
                    "relative error {error} exceeds tolerance {}",
                    asymptotic_tolerance()
                )
            }
            AnalyticDecline::SampleTooSmall => write!(f, "the base sample index is too small"),
            AnalyticDecline::SeriesDeclined => write!(f, "the series expansion declined"),
            AnalyticDecline::NoDominantFactor => write!(f, "no factor attains the radius"),
        }
    }
}

impl core::error::Error for AnalyticDecline {}

// ---------------------------------------------------------------------------
// Polynomial arithmetic over ℚ, least-significant coefficient first
// ---------------------------------------------------------------------------

fn zero() -> BigRational {
    BigRational::zero()
}

fn one() -> BigRational {
    BigRational::one()
}

fn int(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn poly_trim(mut poly: Vec<BigRational>) -> Vec<BigRational> {
    while poly.last().is_some_and(BigRational::is_zero) {
        poly.pop();
    }
    poly
}

/// Degree of a trimmed polynomial, or `None` for the zero polynomial.
fn poly_degree(poly: &[BigRational]) -> Option<usize> {
    let trimmed = poly_trim(poly.to_vec());
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.len() - 1)
    }
}

fn poly_add(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    let len = left.len().max(right.len());
    let mut out = vec![zero(); len];
    for (index, slot) in out.iter_mut().enumerate() {
        if let Some(value) = left.get(index) {
            *slot += value;
        }
        if let Some(value) = right.get(index) {
            *slot += value;
        }
    }
    poly_trim(out)
}

fn poly_mul(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut out = vec![zero(); left.len() + right.len() - 1];
    for (i, a) in left.iter().enumerate() {
        if a.is_zero() {
            continue;
        }
        for (j, b) in right.iter().enumerate() {
            out[i + j] += a * b;
        }
    }
    poly_trim(out)
}

fn poly_scale(poly: &[BigRational], factor: &BigRational) -> Vec<BigRational> {
    poly_trim(poly.iter().map(|c| c * factor).collect())
}

fn poly_eval(poly: &[BigRational], at: &BigRational) -> BigRational {
    let mut acc = zero();
    for coeff in poly.iter().rev() {
        acc = acc * at + coeff;
    }
    acc
}

/// `f(−t)`: negate the odd-degree coefficients.
fn poly_reflect(poly: &[BigRational]) -> Vec<BigRational> {
    poly_trim(
        poly.iter()
            .enumerate()
            .map(|(index, coeff)| {
                if index % 2 == 1 {
                    -coeff
                } else {
                    coeff.clone()
                }
            })
            .collect(),
    )
}

/// `p(t²)`: spread the coefficients over the even degrees.
///
/// The positive real roots of `p(t²)` are exactly the square roots of the
/// positive real roots of `p`, order-preserving, so the *smallest* positive root
/// of `p(t²)` is the square root of the smallest positive root of `p`. That is
/// how [`ModulusRoute::PairwiseResultant`] turns a polynomial in the squared
/// moduli into one in the moduli themselves.
fn poly_substitute_square(poly: &[BigRational]) -> Vec<BigRational> {
    let trimmed = poly_trim(poly.to_vec());
    let mut out = Vec::with_capacity(trimmed.len().saturating_mul(2));
    for (index, coeff) in trimmed.iter().enumerate() {
        if index > 0 {
            out.push(zero());
        }
        out.push(coeff.clone());
    }
    poly_trim(out)
}

/// Scale `poly` by a **positive** rational so that its coefficients are coprime
/// integers.
///
/// Sign variations are what a Sturm chain counts, and a positive scale changes
/// none of them — so normalizing every chain member this way is free of
/// semantic content and keeps the bignum coefficients from doubling in size at
/// each Euclidean step, which is the whole cost of a degree-`n²` chain.
fn poly_primitive(poly: &[BigRational]) -> Vec<BigRational> {
    let trimmed = poly_trim(poly.to_vec());
    if trimmed.is_empty() {
        return trimmed;
    }
    let mut denominator_lcm = BigInt::one();
    for coeff in &trimmed {
        let denominator = coeff.denom().magnitude().clone();
        let gcd = gcd_big(&denominator_lcm.magnitude().clone(), &denominator);
        denominator_lcm = BigInt::from(&denominator_lcm.magnitude().clone() / &gcd * &denominator);
    }
    let scaled: Vec<BigInt> = trimmed
        .iter()
        .map(|coeff| (coeff * BigRational::from_integer(denominator_lcm.clone())).to_integer())
        .collect();
    let mut content = num_bigint::BigUint::from(0u32);
    for value in &scaled {
        content = gcd_big(&content, value.magnitude());
    }
    if content.is_zero() {
        return trimmed;
    }
    let content = BigInt::from(content);
    poly_trim(
        scaled
            .into_iter()
            .map(|value| BigRational::from_integer(value / &content))
            .collect(),
    )
}

/// Binary GCD of two magnitudes, by Euclid.
fn gcd_big(left: &num_bigint::BigUint, right: &num_bigint::BigUint) -> num_bigint::BigUint {
    let mut a = left.clone();
    let mut b = right.clone();
    while !b.is_zero() {
        let remainder = a % &b;
        a = core::mem::replace(&mut b, remainder);
    }
    a
}

fn poly_derivative(poly: &[BigRational]) -> Vec<BigRational> {
    poly_trim(
        poly.iter()
            .enumerate()
            .skip(1)
            .map(|(index, coeff)| coeff * int(i64::try_from(index).unwrap_or(i64::MAX)))
            .collect(),
    )
}

/// Long division; `None` when the divisor is the zero polynomial.
fn poly_divrem(
    numerator: &[BigRational],
    denominator: &[BigRational],
) -> Option<(Vec<BigRational>, Vec<BigRational>)> {
    let denominator = poly_trim(denominator.to_vec());
    let den_degree = poly_degree(&denominator)?;
    let mut remainder = poly_trim(numerator.to_vec());
    let mut quotient: Vec<BigRational> = Vec::new();
    while let Some(rem_degree) = poly_degree(&remainder) {
        if rem_degree < den_degree {
            break;
        }
        let shift = rem_degree - den_degree;
        let factor = &remainder[rem_degree] / &denominator[den_degree];
        if quotient.len() <= shift {
            quotient.resize(shift + 1, zero());
        }
        quotient[shift] += &factor;
        let mut subtrahend = vec![zero(); shift];
        subtrahend.extend(denominator.iter().map(|c| c * &factor));
        remainder = poly_add(&remainder, &poly_scale(&subtrahend, &-one()));
    }
    Some((poly_trim(quotient), remainder))
}

fn poly_monic(poly: &[BigRational]) -> Vec<BigRational> {
    let trimmed = poly_trim(poly.to_vec());
    match poly_degree(&trimmed) {
        None => Vec::new(),
        Some(degree) => {
            let lead = trimmed[degree].clone();
            poly_scale(&trimmed, &(one() / lead))
        }
    }
}

fn poly_gcd(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    let mut a = poly_trim(left.to_vec());
    let mut b = poly_trim(right.to_vec());
    while poly_degree(&b).is_some() {
        let Some((_, remainder)) = poly_divrem(&a, &b) else {
            break;
        };
        a = b;
        // Positive-scale each remainder to a primitive integer polynomial. The
        // gcd is defined up to a unit and the result is made monic below, so
        // this changes nothing about the answer -- it only stops the
        // coefficients doubling in size at every step, which is what makes the
        // degree-`n²` modulus polynomials of `ModulusRoute::PairwiseResultant`
        // affordable at all.
        b = poly_primitive(&remainder);
    }
    poly_monic(&a)
}

/// Extended Euclid over ℚ[x]: returns `(gcd, u, v)` with `u·left + v·right = gcd`
/// and `gcd` monic. `None` when both inputs are zero.
fn poly_ext_gcd(
    left: &[BigRational],
    right: &[BigRational],
) -> Option<(Vec<BigRational>, Vec<BigRational>, Vec<BigRational>)> {
    let mut old_r = poly_trim(left.to_vec());
    let mut r = poly_trim(right.to_vec());
    let mut old_s = vec![one()];
    let mut s: Vec<BigRational> = Vec::new();
    let mut old_t: Vec<BigRational> = Vec::new();
    let mut t = vec![one()];
    while poly_degree(&r).is_some() {
        let (quotient, remainder) = poly_divrem(&old_r, &r)?;
        let next_s = poly_add(&old_s, &poly_scale(&poly_mul(&quotient, &s), &-one()));
        let next_t = poly_add(&old_t, &poly_scale(&poly_mul(&quotient, &t), &-one()));
        old_r = core::mem::replace(&mut r, remainder);
        old_s = core::mem::replace(&mut s, next_s);
        old_t = core::mem::replace(&mut t, next_t);
    }
    let degree = poly_degree(&old_r)?;
    let lead = old_r[degree].clone();
    let inverse = one() / lead;
    Some((
        poly_scale(&old_r, &inverse),
        poly_scale(&old_s, &inverse),
        poly_scale(&old_t, &inverse),
    ))
}

/// The monic square-free part `f / gcd(f, f')`, so every root is simple and a
/// sign change brackets it.
fn poly_squarefree(poly: &[BigRational]) -> Vec<BigRational> {
    let trimmed = poly_trim(poly.to_vec());
    let derivative = poly_derivative(&trimmed);
    if poly_degree(&derivative).is_none() {
        return poly_monic(&trimmed);
    }
    let gcd = poly_gcd(&trimmed, &derivative);
    match poly_divrem(&trimmed, &gcd) {
        Some((quotient, _)) => poly_monic(&quotient),
        None => poly_monic(&trimmed),
    }
}

/// A Cauchy bound: every complex root of `poly` has modulus below the result.
fn cauchy_upper_bound(poly: &[BigRational]) -> Option<BigRational> {
    let degree = poly_degree(poly)?;
    if degree == 0 {
        return None;
    }
    let lead = poly[degree].clone();
    let mut worst = zero();
    for coeff in &poly[..degree] {
        let ratio = (coeff / &lead).abs();
        if ratio > worst {
            worst = ratio;
        }
    }
    Some(worst + one())
}

/// The reciprocal Cauchy bound: every complex root of `poly` has modulus **at
/// least** the result. It is the Cauchy bound applied to the reversed
/// polynomial, whose roots are the reciprocals. `None` when `poly(0) = 0`.
fn reciprocal_cauchy_bound(poly: &[BigRational]) -> Option<BigRational> {
    let degree = poly_degree(poly)?;
    if degree == 0 || poly[0].is_zero() {
        return None;
    }
    let constant = poly[0].clone();
    let mut worst = zero();
    for coeff in &poly[1..=degree] {
        let ratio = (coeff / &constant).abs();
        if ratio > worst {
            worst = ratio;
        }
    }
    Some(one() / (worst + one()))
}

/// The exact integer square root, or `None` when `value` is not a perfect square.
fn integer_sqrt(value: &BigInt) -> Option<BigInt> {
    if value.is_negative() {
        return None;
    }
    if value.is_zero() {
        return Some(BigInt::zero());
    }
    let mut guess = BigInt::one() << (value.bits() / 2 + 1);
    loop {
        let next = (&guess + value / &guess) >> 1u32;
        if next >= guess {
            break;
        }
        guess = next;
    }
    if &guess * &guess == *value {
        Some(guess)
    } else {
        None
    }
}

/// The exact rational square root, or `None` when it is irrational.
fn rational_sqrt(value: &BigRational) -> Option<BigRational> {
    if value.is_negative() {
        return None;
    }
    let numerator = integer_sqrt(value.numer())?;
    let denominator = integer_sqrt(value.denom())?;
    Some(BigRational::new(numerator, denominator))
}

// ---------------------------------------------------------------------------
// Reused root counting
// ---------------------------------------------------------------------------

fn to_machine_poly(poly: &[BigRational]) -> Option<Vec<Rational>> {
    poly.iter().map(Rational::from_big_rational).collect()
}

/// A Sturm root counter for one fixed polynomial.
///
/// Two widths, tried in that order:
///
/// * [`RootCounter::Machine`] is the reuse — [`crate::sturm::count_real_roots_in`]
///   over the crate's `i128` [`Rational`]. It is what every wave-two route used
///   and what still answers every wave-two shape.
/// * [`RootCounter::Big`] is a Sturm chain over [`BigRational`], built once and
///   reused across counts. It exists because the modulus polynomial of
///   [`ModulusRoute::PairwiseResultant`] has degree `2·(deg f)²` — degree 18 for
///   a cubic, 32 for a quartic — and a Sturm chain of that degree leaves `i128`
///   on the second or third remainder, so the machine reuse simply declines
///   there. Each chain member is normalized to a primitive integer polynomial by
///   a **positive** scale, which no sign variation can see.
///
/// The two are held to agree: `bignum_and_machine_sturm_counts_agree` in this
/// module's tests compares them over a family of polynomials both widths can
/// take, so the fallback is not an unchecked second opinion.
enum RootCounter {
    /// The `i128` reuse, with the original polynomial kept so a count that
    /// overflows at some endpoint can still fall through to the bignum chain.
    Machine {
        /// The polynomial narrowed to `i128` rationals.
        machine: Vec<Rational>,
        /// The same polynomial at full width.
        poly: Vec<BigRational>,
    },
    /// A `BigRational` Sturm chain of the square-free part, built once.
    Big(Vec<Vec<BigRational>>),
}

impl RootCounter {
    /// Build a counter for `poly`. `None` only for the zero polynomial, where
    /// every point is a root and there is nothing to count.
    fn new(poly: &[BigRational]) -> Option<Self> {
        let poly = poly_trim(poly.to_vec());
        if let Some(machine) = to_machine_poly(&poly) {
            return Some(RootCounter::Machine { machine, poly });
        }
        Some(RootCounter::Big(sturm_chain_big(&poly)?))
    }

    /// Distinct real roots in the half-open interval `(lower, upper]`.
    fn count(&self, lower: &BigRational, upper: &BigRational) -> Option<usize> {
        match self {
            RootCounter::Machine { machine, poly } => {
                let narrowed = Rational::from_big_rational(lower)
                    .zip(Rational::from_big_rational(upper))
                    .and_then(|(low, high)| crate::sturm::count_real_roots_in(machine, low, high));
                match narrowed {
                    Some(count) => Some(count),
                    // The `i128` chain overflowed. The same count at full width
                    // is still available, at the cost of rebuilding the chain.
                    None => Some(Self::count_big(&sturm_chain_big(poly)?, lower, upper)),
                }
            }
            RootCounter::Big(chain) => Some(Self::count_big(chain, lower, upper)),
        }
    }

    fn count_big(chain: &[Vec<BigRational>], lower: &BigRational, upper: &BigRational) -> usize {
        let at_lower = sign_variations_big(chain, lower);
        let at_upper = sign_variations_big(chain, upper);
        at_lower.saturating_sub(at_upper)
    }
}

/// The Sturm chain `s₀ = squarefree(p)`, `s₁ = s₀′`, `s_{k+1} = −rem(s_{k−1}, s_k)`
/// over [`BigRational`], every member scaled to a primitive integer polynomial by
/// a positive rational. `None` for the zero polynomial.
fn sturm_chain_big(poly: &[BigRational]) -> Option<Vec<Vec<BigRational>>> {
    let first = poly_primitive(&poly_squarefree(poly));
    let degree = poly_degree(&first)?;
    let mut chain = vec![first];
    if degree == 0 {
        return Some(chain); // a nonzero constant: no roots anywhere
    }
    let derivative = poly_primitive(&poly_derivative(&chain[0]));
    if poly_degree(&derivative).is_none() {
        return Some(chain);
    }
    chain.push(derivative);
    // Each remainder drops the degree by at least one, so the chain is bounded.
    while chain.len() <= degree + 2 {
        let len = chain.len();
        let (_, remainder) = poly_divrem(&chain[len - 2], &chain[len - 1])?;
        let remainder = poly_trim(remainder);
        if poly_degree(&remainder).is_none() {
            break;
        }
        chain.push(poly_primitive(&poly_scale(&remainder, &-one())));
    }
    Some(chain)
}

/// Sign changes in the chain at `x`, zeros skipped.
fn sign_variations_big(chain: &[Vec<BigRational>], x: &BigRational) -> usize {
    let mut variations = 0usize;
    let mut previous: Option<bool> = None;
    for member in chain {
        let value = poly_eval(member, x);
        if value.is_zero() {
            continue;
        }
        let positive = value.is_positive();
        if let Some(prev) = previous
            && prev != positive
        {
            variations += 1;
        }
        previous = Some(positive);
    }
    variations
}

/// Distinct real roots of `poly` in the half-open interval `(lower, upper]`.
/// `None` when neither width reaches a count.
fn count_roots_in(poly: &[BigRational], lower: &BigRational, upper: &BigRational) -> Option<usize> {
    RootCounter::new(poly)?.count(lower, upper)
}

/// The number of distinct real roots of `poly`, by
/// [`crate::sturm::isolate_real_roots`]. `None` when that reuse declines.
fn distinct_real_root_count(poly: &[BigRational]) -> Option<usize> {
    let machine = to_machine_poly(poly)?;
    crate::sturm::isolate_real_roots(&machine).map(|intervals| intervals.len())
}

// ---------------------------------------------------------------------------
// The pairwise-product resultant
// ---------------------------------------------------------------------------

/// The Sylvester matrix of two polynomials in `z` whose coefficients are
/// themselves polynomials in `t`, in the convention
/// `axeyum_ir::poly::sylvester_matrix` uses: `deg q` rows of `p`'s coefficients
/// (most significant first) above `deg p` rows of `q`'s.
///
/// The `axeyum-ir` builders are not reusable here — the `i128` one takes the
/// wrong coefficient width and the `BigRational` one is private — so the ten
/// lines are rebuilt, deliberately matching that convention so the determinant
/// primitive below sees the matrix it expects.
fn sylvester_matrix_big(
    p_coeffs: &[Vec<BigRational>],
    q_coeffs: &[Vec<BigRational>],
) -> Option<Vec<Vec<Vec<BigRational>>>> {
    let p_degree = p_coeffs.len().checked_sub(1)?;
    let q_degree = q_coeffs.len().checked_sub(1)?;
    if p_degree == 0 || q_degree == 0 {
        return None;
    }
    let dimension = p_degree + q_degree;
    let mut matrix = vec![vec![vec![zero()]; dimension]; dimension];
    for (row, slot) in matrix.iter_mut().take(q_degree).enumerate() {
        for (column, coeff) in p_coeffs.iter().rev().enumerate() {
            slot[row + column].clone_from(coeff);
        }
    }
    for (row, slot) in matrix.iter_mut().skip(q_degree).take(p_degree).enumerate() {
        for (column, coeff) in q_coeffs.iter().rev().enumerate() {
            slot[row + column].clone_from(coeff);
        }
    }
    Some(matrix)
}

/// The **monic** polynomial whose roots are every pairwise product `rᵢ·rⱼ` of the
/// roots of `factor`, from the resultant
/// `g(t) = Res_z(f(z), zⁿ·f(t/z))`.
///
/// # Why the roots are the pairwise products
///
/// Write `f(z) = aₙ Πᵢ (z − rᵢ)` and `h_t(z) = zⁿ f(t/z) = Σₖ aₖ tᵏ z^{n−k}`,
/// which has degree `n` in `z` exactly because `f(0) = a₀ ≠ 0`. Then
/// `h_t(rᵢ) = rᵢⁿ f(t/rᵢ) = aₙ Πⱼ (t − rᵢrⱼ)`, so
///
/// ```text
/// Res_z(f, h_t) = aₙ^n Πᵢ h_t(rᵢ) = aₙ^{2n} Π_{i,j} (t − rᵢ rⱼ).
/// ```
///
/// # The two identities this checks
///
/// The determinant is computed by `axeyum_ir::poly_big::big_determinant`
/// (exact evaluation–interpolation over `BigRational`). Two exact consequences
/// of the display above are re-checked against it, and a mismatch **declines**
/// rather than answering:
///
/// * `deg g = n²`;
/// * the monic `g` satisfies `g(0) = Π_{i,j}(−rᵢrⱼ) = (−1)ⁿ (a₀/aₙ)^{2n}`, using
///   `Πᵢ rᵢ = (−1)ⁿ a₀/aₙ`.
///
/// Neither identity is how the determinant is computed, so together they are an
/// independent check on the primitive rather than a restatement of it.
fn pairwise_product_resultant(factor: &[BigRational]) -> Option<Vec<BigRational>> {
    let factor = poly_trim(factor.to_vec());
    let degree = poly_degree(&factor)?;
    if degree == 0 || factor[0].is_zero() {
        return None;
    }
    // f(z): coefficients constant in t.
    let p_coeffs: Vec<Vec<BigRational>> = factor.iter().map(|a| vec![a.clone()]).collect();
    // h_t(z) = zⁿ f(t/z): the coefficient of z^j is a_{n−j}·t^{n−j}.
    let q_coeffs: Vec<Vec<BigRational>> = (0..=degree)
        .map(|j| {
            let exponent = degree - j;
            let mut cell = vec![zero(); exponent + 1];
            cell[exponent] = factor[exponent].clone();
            cell
        })
        .collect();
    let matrix = sylvester_matrix_big(&p_coeffs, &q_coeffs)?;
    let determinant = axeyum_ir::poly_big::big_determinant(&matrix);
    accept_pairwise_resultant(&factor, &determinant)
}

/// The two identities of `pairwise_product_resultant`, applied to a candidate
/// determinant: `deg g = n²`, and the monic `g` has
/// `g(0) = (−1)ⁿ (a₀/aₙ)^{2n}`. `Some(monic g)` when both hold, `None` otherwise.
///
/// Split out from the producer so a test can hand it a **corrupted**
/// determinant: a guard whose only input is a value no test can perturb is a
/// guard no test can kill.
fn accept_pairwise_resultant(
    factor: &[BigRational],
    determinant: &[BigRational],
) -> Option<Vec<BigRational>> {
    let factor = poly_trim(factor.to_vec());
    let degree = poly_degree(&factor)?;
    let determinant = poly_trim(determinant.to_vec());
    if poly_degree(&determinant)? != degree * degree {
        return None;
    }
    let monic = poly_monic(&determinant);
    let ratio = &factor[0] / &factor[degree];
    let mut expected = one();
    for _ in 0..(2 * degree) {
        expected *= &ratio;
    }
    if degree % 2 == 1 {
        expected = -expected;
    }
    if monic[0] != expected {
        return None;
    }
    Some(monic)
}

/// The modulus polynomial [`ModulusRoute::PairwiseResultant`] defines for
/// `factor`: the square-free part of `pairwise_product_resultant`, with `t`
/// substituted by `t²`, made monic.
///
/// Its smallest positive real root is the smallest modulus of a root of
/// `factor` — see the module documentation for the theorem and its proof.
///
/// The square-free reduction happens **before** the substitution and is not
/// cosmetic: for `Φ₅` it takes the degree-16 resultant `(t−1)⁴·Φ₅(t)³` down to
/// `t⁵ − 1`, so the Sturm chain that follows runs at degree 10 rather than 32.
fn resultant_modulus_polynomial(factor: &[BigRational]) -> Option<Vec<BigRational>> {
    let resultant = pairwise_product_resultant(factor)?;
    let squarefree = poly_squarefree(&resultant);
    let substituted = poly_monic(&poly_substitute_square(&squarefree));
    if poly_eval(&substituted, &zero()).is_zero() {
        return None;
    }
    Some(substituted)
}

// ---------------------------------------------------------------------------
// Per-factor modulus bounds
// ---------------------------------------------------------------------------

/// How the minimal modulus of one factor's roots was decided.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModulusRoute {
    /// Every root of the factor is real: Sturm finds `deg f` distinct real
    /// roots. The moduli are then exactly the positive real roots of
    /// `g(t) = f(t)·f(−t)`, so the minimal modulus is `g`'s smallest positive
    /// root. **Exact.**
    AllRealRoots,
    /// A degree-two factor with negative discriminant: its two roots are a
    /// complex-conjugate pair whose common modulus is `√(c/a)`, the positive
    /// root of `g(t) = t² − c/a`. **Exact**, and the case `1/(1+x²)` on which a
    /// real-roots-only route is simply wrong.
    ConjugatePair,
    /// Any factor with `f(0) ≠ 0` and degree at most
    /// `MAX_RESULTANT_FACTOR_DEGREE`, including one whose roots are complex
    /// and irrational and whose degree is odd. The modulus polynomial is the
    /// square-free part of `g(t) = Res_z(f(z), zⁿ f(t/z))` — whose roots are
    /// every pairwise product `rᵢrⱼ` — with `t` substituted by `t²`. Its
    /// smallest positive root is `minᵢ |rᵢ|`. **Exact**, and the case `Φ₅` on
    /// which the two wave-two routes gave a lower bound of `1/2` where the
    /// truth is `1`.
    PairwiseResultant,
    /// Neither exact route applies. Only the reciprocal Cauchy bound
    /// `1/(1 + maxᵢ≥₁|aᵢ/a₀|)` is certified, which is a **lower bound** on every
    /// root's modulus and therefore on the radius.
    ReciprocalCauchy,
}

/// One irreducible factor of the reduced denominator together with what is
/// certified about the modulus of its roots.
///
/// The fields are public because a certificate is data, not a promise:
/// [`verify`](FactorModulusBound::verify) is the judge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorModulusBound {
    /// The factor, least-significant coefficient first.
    pub factor: Vec<BigRational>,
    /// Its multiplicity in the reduced denominator.
    pub multiplicity: u32,
    /// Which route decided the modulus.
    pub route: ModulusRoute,
    /// `f(t)·f(−t)` for [`ModulusRoute::AllRealRoots`], `t² − c/a` for
    /// [`ModulusRoute::ConjugatePair`], and empty for
    /// [`ModulusRoute::ReciprocalCauchy`]. Its positive real roots are exactly
    /// the moduli of the factor's roots on the two exact routes.
    pub modulus_polynomial: Vec<BigRational>,
    /// A certified rational lower bound: every root of `factor` has modulus
    /// strictly greater than this.
    pub lower: BigRational,
}

impl FactorModulusBound {
    /// Whether this factor's modulus is pinned exactly (as opposed to bounded).
    pub fn is_exact(&self) -> bool {
        !matches!(self.route, ModulusRoute::ReciprocalCauchy)
    }

    /// Re-derive everything this bound asserts from the factor's coefficients.
    ///
    /// `index` names the factor in any error raised, so a refusal points at the
    /// offending factor rather than at the certificate as a whole.
    ///
    /// # Errors
    ///
    /// Refuses a constant factor, a factor vanishing at the origin, a
    /// non-positive lower bound, a route whose precondition fails, a modulus
    /// polynomial that is not the one the route defines, and a lower bound the
    /// route does not certify.
    pub fn verify(&self, index: usize) -> Result<(), AnalyticError> {
        let factor = poly_trim(self.factor.clone());
        let degree =
            poly_degree(&factor).ok_or(AnalyticError::FactorIsConstant { factor: index })?;
        if degree == 0 {
            return Err(AnalyticError::FactorIsConstant { factor: index });
        }
        if factor[0].is_zero() {
            return Err(AnalyticError::FactorVanishesAtZero { factor: index });
        }
        if !self.lower.is_positive() {
            return Err(AnalyticError::NonPositiveBound);
        }
        match self.route {
            ModulusRoute::AllRealRoots => {
                let real = distinct_real_root_count(&factor).ok_or(AnalyticError::SturmDeclined)?;
                if real != degree {
                    return Err(AnalyticError::RouteNotApplicable { factor: index });
                }
                let expected = poly_mul(&factor, &poly_reflect(&factor));
                if poly_trim(self.modulus_polynomial.clone()) != expected {
                    return Err(AnalyticError::ModulusPolynomialMismatch { factor: index });
                }
                // No modulus below `lower`: Sturm finds no root of `g` in
                // `(0, lower]`, and `g`'s positive roots are exactly the moduli.
                let below = count_roots_in(&expected, &zero(), &self.lower)
                    .ok_or(AnalyticError::SturmDeclined)?;
                if below != 0 {
                    return Err(AnalyticError::LowerBoundNotCertified { factor: index });
                }
                Ok(())
            }
            ModulusRoute::ConjugatePair => {
                if degree != 2 {
                    return Err(AnalyticError::RouteNotApplicable { factor: index });
                }
                let (c, b, a) = (factor[0].clone(), factor[1].clone(), factor[2].clone());
                let discriminant = &b * &b - int(4) * &a * &c;
                if !discriminant.is_negative() {
                    return Err(AnalyticError::RouteNotApplicable { factor: index });
                }
                let modulus_squared = &c / &a;
                let expected = vec![-modulus_squared.clone(), zero(), one()];
                if poly_trim(self.modulus_polynomial.clone()) != poly_trim(expected) {
                    return Err(AnalyticError::ModulusPolynomialMismatch { factor: index });
                }
                if &self.lower * &self.lower >= modulus_squared {
                    return Err(AnalyticError::LowerBoundNotCertified { factor: index });
                }
                Ok(())
            }
            ModulusRoute::PairwiseResultant => {
                if degree > MAX_RESULTANT_FACTOR_DEGREE {
                    return Err(AnalyticError::RouteNotApplicable { factor: index });
                }
                let expected = resultant_modulus_polynomial(&factor)
                    .ok_or(AnalyticError::ResultantDeclined { factor: index })?;
                if poly_monic(&self.modulus_polynomial) != expected {
                    return Err(AnalyticError::ModulusPolynomialMismatch { factor: index });
                }
                // No modulus below `lower`: the smallest positive root of the
                // modulus polynomial IS the smallest modulus, so no positive
                // root there means no root of the factor there either.
                let below = count_roots_in(&expected, &zero(), &self.lower)
                    .ok_or(AnalyticError::SturmDeclined)?;
                if below != 0 {
                    return Err(AnalyticError::LowerBoundNotCertified { factor: index });
                }
                Ok(())
            }
            ModulusRoute::ReciprocalCauchy => {
                if !self.modulus_polynomial.is_empty() {
                    return Err(AnalyticError::ModulusPolynomialMismatch { factor: index });
                }
                let bound = reciprocal_cauchy_bound(&factor)
                    .ok_or(AnalyticError::RouteNotApplicable { factor: index })?;
                if self.lower > bound {
                    return Err(AnalyticError::LowerBoundNotCertified { factor: index });
                }
                Ok(())
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The radius
// ---------------------------------------------------------------------------

/// An irrational radius, pinned exactly.
///
/// The radius is the unique root of `polynomial` in the Sturm-certified bracket
/// `(coarse_lower, coarse_upper]`, refined to `[lower, upper]` by a sign change
/// of that polynomial's square-free part — a refinement that costs only exact
/// rational evaluation, so the Sturm chain is never asked for a deeper bracket
/// than the coarse one it already certified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgebraicRadius {
    /// The global modulus polynomial `G = Π g`, whose smallest positive root is
    /// the radius.
    pub polynomial: Vec<BigRational>,
    /// Sturm-certified: `G` has no root in `(0, coarse_lower]`.
    pub coarse_lower: BigRational,
    /// Sturm-certified: `G` has exactly one root in
    /// `(coarse_lower, coarse_upper]`.
    pub coarse_upper: BigRational,
    /// Refined lower endpoint, inside the coarse bracket.
    pub lower: BigRational,
    /// Refined upper endpoint, inside the coarse bracket.
    pub upper: BigRational,
}

/// What is known about the radius of convergence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RadiusOfConvergence {
    /// The reduced denominator is constant, so the series is a polynomial and
    /// converges everywhere.
    Infinite,
    /// The radius is exactly this rational.
    Exact(BigRational),
    /// The radius is irrational; see [`AlgebraicRadius`]. Boxed because it is
    /// several times the size of every other variant.
    Algebraic(Box<AlgebraicRadius>),
    /// Some factor reached no exact route, so only this rational lower bound on
    /// the radius is certified. The true radius is at least this.
    LowerBound(BigRational),
}

impl RadiusOfConvergence {
    /// A rational lower bound on the radius, available in every case except
    /// [`Infinite`](RadiusOfConvergence::Infinite).
    pub fn lower_bound(&self) -> Option<BigRational> {
        match self {
            RadiusOfConvergence::Infinite => None,
            RadiusOfConvergence::Exact(value) | RadiusOfConvergence::LowerBound(value) => {
                Some(value.clone())
            }
            RadiusOfConvergence::Algebraic(data) => Some(data.lower.clone()),
        }
    }

    /// The certified rational bracket around an exactly known radius, or `None`
    /// when the radius is infinite or only bounded below.
    pub fn bracket(&self) -> Option<(BigRational, BigRational)> {
        match self {
            RadiusOfConvergence::Exact(value) => Some((value.clone(), value.clone())),
            RadiusOfConvergence::Algebraic(data) => Some((data.lower.clone(), data.upper.clone())),
            RadiusOfConvergence::Infinite | RadiusOfConvergence::LowerBound(_) => None,
        }
    }
}

/// The radius of convergence of a rational power series, with everything needed
/// to re-derive it.
///
/// The claim, in full: `p/q` reduces to `reduced_numerator / reduced_denominator`
/// by cancelling `common_factor`; the two reduced parts are coprime (witnessed
/// by the Bézout pair, so no singularity was silently cancelled away); the
/// reduced denominator is `content · Π factorᵐ`; each factor's roots have the
/// modulus behaviour its [`FactorModulusBound`] states; and [`radius`] follows.
///
/// [`radius`]: RadiusCertificate::radius
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RadiusCertificate {
    /// The numerator as supplied, least-significant first.
    pub numerator: Vec<BigRational>,
    /// The denominator as supplied, least-significant first, with `q(0) ≠ 0`.
    pub denominator: Vec<BigRational>,
    /// The monic `gcd(p, q)` that was cancelled.
    pub common_factor: Vec<BigRational>,
    /// `p / common_factor`.
    pub reduced_numerator: Vec<BigRational>,
    /// `q / common_factor`.
    pub reduced_denominator: Vec<BigRational>,
    /// `u` in `u·reduced_numerator + v·reduced_denominator = 1`.
    pub bezout_numerator: Vec<BigRational>,
    /// `v` in `u·reduced_numerator + v·reduced_denominator = 1`.
    pub bezout_denominator: Vec<BigRational>,
    /// The leading content of the factorization of the reduced denominator.
    pub content: BigRational,
    /// Its factors, with what each certifies about the modulus of its roots.
    pub factors: Vec<FactorModulusBound>,
    /// The conclusion.
    pub radius: RadiusOfConvergence,
}

impl RadiusCertificate {
    /// Re-derive every step of the claim.
    ///
    /// Runs, in order: the denominator's side conditions; the two split
    /// identities `gcd · reduced = original`; the Bézout witness for
    /// coprimality; the re-multiplied factorization; each per-factor bound; and
    /// finally the conclusion, which for an exact radius means recomputing
    /// `G = Π g` and asking Sturm for the root counts that pin its smallest
    /// positive root.
    ///
    /// # Errors
    ///
    /// One [`AnalyticError`] per guard; see that type. A
    /// [`AnalyticError::SturmDeclined`] is not a refutation — it means the
    /// reused root counter gave up.
    pub fn verify(&self) -> Result<(), AnalyticError> {
        let denominator = poly_trim(self.denominator.clone());
        if poly_degree(&denominator).is_none() {
            return Err(AnalyticError::EmptyDenominator);
        }
        if denominator[0].is_zero() {
            return Err(AnalyticError::DenominatorVanishesAtZero);
        }

        // The two split identities.
        let numerator = poly_trim(self.numerator.clone());
        let rebuilt_numerator = poly_mul(&self.common_factor, &self.reduced_numerator);
        if let Some(degree) = first_disagreement(&rebuilt_numerator, &numerator) {
            return Err(AnalyticError::NumeratorSplitMismatch { degree });
        }
        let rebuilt_denominator = poly_mul(&self.common_factor, &self.reduced_denominator);
        if let Some(degree) = first_disagreement(&rebuilt_denominator, &denominator) {
            return Err(AnalyticError::DenominatorSplitMismatch { degree });
        }

        // Coprimality of the reduced pair: without it a pole of the reduced
        // denominator could be cancelled by the numerator and the radius would
        // be understated.
        let bezout = poly_add(
            &poly_mul(&self.bezout_numerator, &self.reduced_numerator),
            &poly_mul(&self.bezout_denominator, &self.reduced_denominator),
        );
        if poly_trim(bezout) != vec![one()] {
            return Err(AnalyticError::NotCoprime);
        }

        // The factorization, re-multiplied.
        if self.content.is_zero() {
            return Err(AnalyticError::ZeroContent);
        }
        let mut product = vec![self.content.clone()];
        for bound in &self.factors {
            for _ in 0..bound.multiplicity {
                product = poly_mul(&product, &bound.factor);
            }
        }
        let reduced_denominator = poly_trim(self.reduced_denominator.clone());
        if let Some(degree) = first_disagreement(&product, &reduced_denominator) {
            return Err(AnalyticError::FactorProductMismatch { degree });
        }

        // Every per-factor bound, from that factor's coefficients alone.
        for (index, bound) in self.factors.iter().enumerate() {
            bound.verify(index)?;
        }

        self.verify_conclusion(&reduced_denominator)
    }

    fn verify_conclusion(&self, reduced_denominator: &[BigRational]) -> Result<(), AnalyticError> {
        match &self.radius {
            RadiusOfConvergence::Infinite => {
                if poly_degree(reduced_denominator) == Some(0) {
                    Ok(())
                } else {
                    Err(AnalyticError::RadiusNotExact)
                }
            }
            RadiusOfConvergence::LowerBound(bound) => {
                if !bound.is_positive() {
                    return Err(AnalyticError::NonPositiveBound);
                }
                for (index, factor) in self.factors.iter().enumerate() {
                    if *bound > factor.lower {
                        return Err(AnalyticError::LowerBoundExceedsFactor { factor: index });
                    }
                }
                Ok(())
            }
            RadiusOfConvergence::Exact(value) => {
                let global = self.global_modulus_polynomial()?;
                if !value.is_positive() {
                    return Err(AnalyticError::NonPositiveBound);
                }
                if !poly_eval(&global, value).is_zero() {
                    return Err(AnalyticError::NotARoot);
                }
                // Exactly one root of `G` in `(0, value]` makes `value` the
                // smallest positive root, hence the smallest modulus.
                let counter = RootCounter::new(&global).ok_or(AnalyticError::SturmDeclined)?;
                let count = counter
                    .count(&zero(), value)
                    .ok_or(AnalyticError::SturmDeclined)?;
                if count != 1 {
                    return Err(AnalyticError::RootCountMismatch {
                        expected: 1,
                        found: count,
                    });
                }
                Ok(())
            }
            RadiusOfConvergence::Algebraic(data) => {
                let AlgebraicRadius {
                    polynomial,
                    coarse_lower,
                    coarse_upper,
                    lower,
                    upper,
                } = data.as_ref();
                let global = self.global_modulus_polynomial()?;
                if poly_trim(polynomial.clone()) != global {
                    return Err(AnalyticError::GlobalModulusMismatch);
                }
                if !coarse_lower.is_positive()
                    || coarse_lower >= coarse_upper
                    || lower < coarse_lower
                    || lower >= upper
                    || upper > coarse_upper
                {
                    return Err(AnalyticError::MalformedBracket);
                }
                let counter = RootCounter::new(&global).ok_or(AnalyticError::SturmDeclined)?;
                let below = counter
                    .count(&zero(), coarse_lower)
                    .ok_or(AnalyticError::SturmDeclined)?;
                if below != 0 {
                    return Err(AnalyticError::RootCountMismatch {
                        expected: 0,
                        found: below,
                    });
                }
                let inside = counter
                    .count(coarse_lower, coarse_upper)
                    .ok_or(AnalyticError::SturmDeclined)?;
                if inside != 1 {
                    return Err(AnalyticError::RootCountMismatch {
                        expected: 1,
                        found: inside,
                    });
                }
                // One root in the coarse bracket, and a sign change of the
                // square-free part on the refined one: the root is in `[lower,
                // upper]`.
                let squarefree = poly_squarefree(&global);
                let at_lower = poly_eval(&squarefree, lower);
                let at_upper = poly_eval(&squarefree, upper);
                if !(at_lower * at_upper).is_negative() {
                    return Err(AnalyticError::NoSignChange);
                }
                Ok(())
            }
        }
    }

    /// `G = Π g` over the factors, refusing when any factor is bound-only (so an
    /// exact claim cannot rest on an incomplete product) or when `G(0) = 0`.
    fn global_modulus_polynomial(&self) -> Result<Vec<BigRational>, AnalyticError> {
        let mut global = vec![one()];
        for (index, bound) in self.factors.iter().enumerate() {
            if !bound.is_exact() {
                return Err(AnalyticError::InexactRoute { factor: index });
            }
            global = poly_mul(&global, &bound.modulus_polynomial);
        }
        if poly_eval(&global, &zero()).is_zero() {
            return Err(AnalyticError::ModulusVanishesAtZero);
        }
        Ok(global)
    }
}

/// The lowest degree at which two trimmed polynomials disagree, or `None` when
/// they are equal.
fn first_disagreement(left: &[BigRational], right: &[BigRational]) -> Option<usize> {
    let left = poly_trim(left.to_vec());
    let right = poly_trim(right.to_vec());
    let len = left.len().max(right.len());
    let nil = zero();
    (0..len).find(|&degree| left.get(degree).unwrap_or(&nil) != right.get(degree).unwrap_or(&nil))
}

/// The radius of convergence of `numerator / denominator`, with a certificate.
///
/// The result is **certified**: an [`RadiusOfConvergence::Exact`] or
/// [`RadiusOfConvergence::Algebraic`] answer *is* the radius, an
/// [`RadiusOfConvergence::LowerBound`] answer is a proved lower bound on it, and
/// [`RadiusCertificate::verify`] re-derives whichever was returned without
/// consulting how it was found.
///
/// # Errors
///
/// Declines with an [`AnalyticDecline`] when the denominator vanishes at the
/// origin, when the reused factorizer or Sturm counter gives up (coefficients
/// outside `i128`, or their own caps), or when isolation does not converge. A
/// decline never means "the radius is not what you think"; it means this route
/// did not reach it.
pub fn radius_of_convergence(
    numerator: &[BigRational],
    denominator: &[BigRational],
) -> Result<RadiusCertificate, AnalyticDecline> {
    let numerator = poly_trim(numerator.to_vec());
    let denominator = poly_trim(denominator.to_vec());
    if poly_degree(&denominator).is_none() {
        return Err(AnalyticDecline::EmptyDenominator);
    }
    if denominator[0].is_zero() {
        return Err(AnalyticDecline::SingularAtZero);
    }

    let common_factor = poly_gcd(&numerator, &denominator);
    let (reduced_numerator, _) =
        poly_divrem(&numerator, &common_factor).ok_or(AnalyticDecline::EmptyDenominator)?;
    let (reduced_denominator, _) =
        poly_divrem(&denominator, &common_factor).ok_or(AnalyticDecline::EmptyDenominator)?;
    let (bezout_gcd, bezout_numerator, bezout_denominator) =
        poly_ext_gcd(&reduced_numerator, &reduced_denominator)
            .ok_or(AnalyticDecline::EmptyDenominator)?;
    if poly_trim(bezout_gcd) != vec![one()] {
        return Err(AnalyticDecline::CertificateRefused(
            AnalyticError::NotCoprime,
        ));
    }

    let degree = poly_degree(&reduced_denominator).ok_or(AnalyticDecline::EmptyDenominator)?;
    if degree == 0 {
        let certificate = RadiusCertificate {
            numerator,
            denominator,
            common_factor,
            reduced_numerator,
            reduced_denominator: reduced_denominator.clone(),
            bezout_numerator,
            bezout_denominator,
            content: reduced_denominator[0].clone(),
            factors: Vec::new(),
            radius: RadiusOfConvergence::Infinite,
        };
        certificate
            .verify()
            .map_err(AnalyticDecline::CertificateRefused)?;
        return Ok(certificate);
    }

    let (content, factors) = factor_with_content(&reduced_denominator)?;
    let bounds = factors
        .into_iter()
        .map(|(factor, multiplicity)| factor_modulus_bound(&factor, multiplicity))
        .collect::<Result<Vec<_>, _>>()?;

    let radius = if bounds.iter().all(FactorModulusBound::is_exact) {
        exact_radius(&bounds)?
    } else {
        let bound = bounds
            .iter()
            .map(|entry| entry.lower.clone())
            .min()
            .ok_or(AnalyticDecline::EmptyDenominator)?;
        RadiusOfConvergence::LowerBound(bound)
    };

    let certificate = RadiusCertificate {
        numerator,
        denominator,
        common_factor,
        reduced_numerator,
        reduced_denominator,
        bezout_numerator,
        bezout_denominator,
        content,
        factors: bounds,
        radius,
    };
    certificate
        .verify()
        .map_err(AnalyticDecline::CertificateRefused)?;
    Ok(certificate)
}

/// A factorization over ℚ: the leading content, then the factors paired with
/// their multiplicities.
type FactorizationOverQ = (BigRational, Vec<(Vec<BigRational>, u32)>);

/// Factor over ℚ by reusing `crate::factor_int::factor_univariate_over_q`, and
/// recover the leading content the factorizer normalizes away.
fn factor_with_content(poly: &[BigRational]) -> Result<FactorizationOverQ, AnalyticDecline> {
    let machine = to_machine_poly(poly).ok_or(AnalyticDecline::FactorizationDeclined)?;
    let factored = crate::factor_int::factor_univariate_over_q(&machine)
        .ok_or(AnalyticDecline::FactorizationDeclined)?;
    let mut factors: Vec<(Vec<BigRational>, u32)> = Vec::new();
    let mut product = vec![one()];
    for (factor, multiplicity) in factored {
        let widened: Vec<BigRational> = factor.iter().map(|c| c.to_big_rational()).collect();
        for _ in 0..multiplicity {
            product = poly_mul(&product, &widened);
        }
        factors.push((widened, multiplicity));
    }
    let degree = poly_degree(poly).ok_or(AnalyticDecline::FactorizationDeclined)?;
    let product_degree = poly_degree(&product).ok_or(AnalyticDecline::FactorizationDeclined)?;
    if product_degree != degree {
        return Err(AnalyticDecline::FactorizationDeclined);
    }
    let content = &poly[degree] / &product[product_degree];
    Ok((content, factors))
}

/// Decide the strongest available modulus route for one factor.
fn factor_modulus_bound(
    factor: &[BigRational],
    multiplicity: u32,
) -> Result<FactorModulusBound, AnalyticDecline> {
    let factor = poly_trim(factor.to_vec());
    let degree = poly_degree(&factor).ok_or(AnalyticDecline::FactorizationDeclined)?;
    if degree == 0 || factor[0].is_zero() {
        return Err(AnalyticDecline::FactorizationDeclined);
    }
    let fallback = reciprocal_cauchy_bound(&factor).ok_or(AnalyticDecline::SturmDeclined)?;

    // The conjugate-pair route first: it is exact and needs no root counting.
    if degree == 2 {
        let (c, b, a) = (factor[0].clone(), factor[1].clone(), factor[2].clone());
        let discriminant = &b * &b - int(4) * &a * &c;
        if discriminant.is_negative() {
            let modulus_squared = &c / &a;
            let lower = strict_lower_bound_for_square(&modulus_squared, &fallback);
            return Ok(FactorModulusBound {
                factor,
                multiplicity,
                route: ModulusRoute::ConjugatePair,
                modulus_polynomial: vec![-modulus_squared, zero(), one()],
                lower,
            });
        }
    }

    let real = distinct_real_root_count(&factor).ok_or(AnalyticDecline::SturmDeclined)?;
    if real == degree {
        let modulus_polynomial = poly_mul(&factor, &poly_reflect(&factor));
        // The reciprocal Cauchy bound already excludes every root below it, so
        // it doubles as the certified lower bound on this route.
        let lower = fallback;
        let below = count_roots_in(&modulus_polynomial, &zero(), &lower)
            .ok_or(AnalyticDecline::SturmDeclined)?;
        if below != 0 {
            return Err(AnalyticDecline::SturmDeclined);
        }
        return Ok(FactorModulusBound {
            factor,
            multiplicity,
            route: ModulusRoute::AllRealRoots,
            modulus_polynomial,
            lower,
        });
    }

    // The general route. It subsumes both routes above -- they are kept because
    // they are far cheaper and answer most shapes -- and it is the only one that
    // reaches an irreducible factor of odd degree with complex roots.
    if degree <= MAX_RESULTANT_FACTOR_DEGREE
        && let Some(modulus_polynomial) = resultant_modulus_polynomial(&factor)
    {
        // The `lower` bound is NOT re-checked here. `radius_of_convergence`
        // runs `RadiusCertificate::verify` over what this returns, and that
        // re-runs the Sturm count on exactly this polynomial and this bound —
        // so a producer-side copy would be a guard no test could ever kill.
        return Ok(FactorModulusBound {
            factor,
            multiplicity,
            route: ModulusRoute::PairwiseResultant,
            modulus_polynomial,
            lower: fallback,
        });
    }

    Ok(FactorModulusBound {
        factor,
        multiplicity,
        route: ModulusRoute::ReciprocalCauchy,
        modulus_polynomial: Vec::new(),
        lower: fallback,
    })
}

/// A positive rational strictly below `√value`, starting from `fallback` (which
/// is already a certified lower bound) and tightening by bisection.
fn strict_lower_bound_for_square(value: &BigRational, fallback: &BigRational) -> BigRational {
    let mut low = fallback.clone();
    let mut high = value + one();
    for _ in 0..32 {
        let mid = (&low + &high) / int(2);
        if &mid * &mid < *value {
            low = mid;
        } else {
            high = mid;
        }
    }
    low
}

/// Isolate the smallest positive root of `G = Π g` and package it as an exact
/// radius.
fn exact_radius(bounds: &[FactorModulusBound]) -> Result<RadiusOfConvergence, AnalyticDecline> {
    let mut global = vec![one()];
    for bound in bounds {
        global = poly_mul(&global, &bound.modulus_polynomial);
    }
    let upper = cauchy_upper_bound(&global).ok_or(AnalyticDecline::IsolationDeclined)?;
    // One Sturm chain for the whole isolation. At the degrees
    // `ModulusRoute::PairwiseResultant` reaches, rebuilding it per count is the
    // dominant cost of the route.
    let counter = RootCounter::new(&global).ok_or(AnalyticDecline::IsolationDeclined)?;

    // An exactly rational radius is often a modulus one of the factors already
    // names: a rational root of a linear factor, or the square root of a
    // conjugate pair's constant ratio when that square root is rational.
    let mut candidates: Vec<BigRational> = Vec::new();
    for bound in bounds {
        match bound.route {
            ModulusRoute::AllRealRoots if poly_degree(&bound.factor) == Some(1) => {
                candidates.push((&bound.factor[0] / &bound.factor[1]).abs());
            }
            ModulusRoute::ConjugatePair => {
                let modulus_squared = &bound.factor[0] / &bound.factor[2];
                if let Some(root) = rational_sqrt(&modulus_squared) {
                    candidates.push(root);
                }
            }
            _ => {}
        }
    }
    candidates.sort();
    candidates.dedup();
    for candidate in &candidates {
        if !candidate.is_positive() {
            continue;
        }
        if !poly_eval(&global, candidate).is_zero() {
            continue;
        }
        let count = counter
            .count(&zero(), candidate)
            .ok_or(AnalyticDecline::SturmDeclined)?;
        if count == 1 {
            return Ok(RadiusOfConvergence::Exact(candidate.clone()));
        }
    }

    // Otherwise bisect, always keeping the leftmost half that still contains a
    // root, so the interval converges on the *smallest* positive root.
    let mut low = zero();
    let mut high = upper;
    let mut isolated = false;
    for _ in 0..128 {
        let count = counter
            .count(&low, &high)
            .ok_or(AnalyticDecline::SturmDeclined)?;
        if count == 0 {
            return Err(AnalyticDecline::IsolationDeclined);
        }
        if count == 1 && low.is_positive() {
            isolated = true;
            break;
        }
        let mid = (&low + &high) / int(2);
        let left = counter
            .count(&low, &mid)
            .ok_or(AnalyticDecline::SturmDeclined)?;
        if left >= 1 {
            high = mid;
        } else {
            low = mid;
        }
    }
    if !isolated {
        return Err(AnalyticDecline::IsolationDeclined);
    }
    if poly_eval(&global, &high).is_zero() {
        return Ok(RadiusOfConvergence::Exact(high));
    }

    // Refine by sign change on the square-free part: exact rational evaluation
    // only, so the Sturm chain is never asked for a deeper bracket than the
    // coarse one it already certified.
    let squarefree = poly_squarefree(&global);
    let (mut lower, mut upper_refined) = (low.clone(), high.clone());
    let sign_low = poly_eval(&squarefree, &lower).is_negative();
    for _ in 0..REFINEMENT_BITS {
        let mid = (&lower + &upper_refined) / int(2);
        let value = poly_eval(&squarefree, &mid);
        if value.is_zero() {
            return Ok(RadiusOfConvergence::Exact(mid));
        }
        if value.is_negative() == sign_low {
            lower = mid;
        } else {
            upper_refined = mid;
        }
    }
    Ok(RadiusOfConvergence::Algebraic(Box::new(AlgebraicRadius {
        polynomial: global,
        coarse_lower: low,
        coarse_upper: high,
        lower,
        upper: upper_refined,
    })))
}

// ---------------------------------------------------------------------------
// Coefficient asymptotics
// ---------------------------------------------------------------------------

/// Sampled evidence that `[xⁿ] p/q ≈ C·nᵏ·ρ⁻ⁿ`.
///
/// # What this is, and what it is not
///
/// This certificate is labelled **`asymptotic-verified-at-finite-n`**, never
/// *certified*. `verify` re-derives, from the carried data alone, that the
/// normalised quantity
///
/// ```text
/// rᵢ = a(nᵢ) · ρ̃^nᵢ / nᵢ^k
/// ```
///
/// takes the three carried values at `n = N, 2N, 4N`, and that the relative
/// spread `eᵢ = |rᵢ/r₃ − 1|` shrinks along those samples and finishes inside the
/// stated tolerance. That is *evidence for* the asymptotic form; it is not a
/// proof of a limit. **No finite sample can be one**, which is exactly why the
/// label is different from the one [`RadiusCertificate`] carries: the radius is
/// pinned by Sturm counts that hold for all `n`, and this is not.
///
/// What *is* certified inside it: the radius (through the nested
/// [`RadiusCertificate`]), the exponent `k` (re-derived as one less than the
/// multiplicity of the dominant factors), and every coefficient (recomputed from
/// [`FormalPowerSeries::from_rational_function`], whose own truncation identity
/// is re-checked).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoefficientAsymptotics {
    /// The numerator, least-significant first.
    pub numerator: Vec<BigRational>,
    /// The denominator, least-significant first.
    pub denominator: Vec<BigRational>,
    /// The certified radius the form rests on.
    pub radius: RadiusCertificate,
    /// The rational stand-in `ρ̃` for the radius, inside its certified bracket.
    pub rho: BigRational,
    /// The polynomial-growth exponent `k`, one less than the multiplicity of the
    /// dominant factors.
    pub exponent: u32,
    /// The three sample indices `N, 2N, 4N`.
    pub samples: Vec<usize>,
    /// The exact coefficients `a(N), a(2N), a(4N)`.
    pub coefficients: Vec<BigRational>,
    /// `rᵢ = a(nᵢ)·ρ̃^nᵢ / nᵢ^k`, which converge to `C`.
    pub ratios: Vec<BigRational>,
    /// `eᵢ = |rᵢ/r₃ − 1|`, the relative spread against the finest sample.
    pub relative_errors: Vec<BigRational>,
    /// The tolerance `e₁` had to meet. `verify` refuses a tolerance looser than
    /// this module's own cap, so widening the claim buys nothing.
    pub tolerance: BigRational,
}

impl CoefficientAsymptotics {
    /// Re-derive the radius, the exponent, the coefficients, the ratios and the
    /// relative errors, and re-check the shrinking condition.
    ///
    /// # Errors
    ///
    /// One [`AnalyticError`] per guard: a radius that is only bounded, a `ρ̃`
    /// outside its bracket, samples that are not `N, 2N, 4N`, a coefficient or
    /// ratio that does not recompute, errors that fail to shrink, a tolerance
    /// above the cap, or an exponent that disagrees with the factorization.
    pub fn verify(&self) -> Result<(), AnalyticError> {
        self.radius.verify()?;
        if self.radius.numerator != poly_trim(self.numerator.clone())
            || self.radius.denominator != poly_trim(self.denominator.clone())
        {
            return Err(AnalyticError::FunctionMismatch);
        }
        if self.samples.len() != 3
            || self.coefficients.len() != 3
            || self.ratios.len() != 3
            || self.relative_errors.len() != 3
        {
            return Err(AnalyticError::MalformedSamples);
        }
        let base = self.samples[0];
        if base < 4 || self.samples[1] != 2 * base || self.samples[2] != 4 * base {
            return Err(AnalyticError::MalformedSamples);
        }

        let (bracket_lower, bracket_upper) = self
            .radius
            .radius
            .bracket()
            .ok_or(AnalyticError::RadiusNotExact)?;
        if self.rho < bracket_lower || self.rho > bracket_upper {
            return Err(AnalyticError::RhoOutsideBracket);
        }

        let derived = dominant_exponent(&self.radius)?;
        if derived != self.exponent {
            return Err(AnalyticError::ExponentMismatch {
                declared: self.exponent,
                derived,
            });
        }

        if !self.tolerance.is_positive() || self.tolerance > tolerance_cap() {
            return Err(AnalyticError::ToleranceTooLoose);
        }

        let (series, identity) = FormalPowerSeries::from_rational_function(
            &self.numerator,
            &self.denominator,
            self.samples[2],
        )
        .ok_or(AnalyticError::SeriesDeclined)?;
        identity
            .verify()
            .map_err(AnalyticError::SeriesCertificate)?;

        let mut ratios = Vec::with_capacity(3);
        for (index, &sample) in self.samples.iter().enumerate() {
            let coefficient = series
                .coefficient(sample)
                .ok_or(AnalyticError::SeriesDeclined)?;
            if *coefficient != self.coefficients[index] {
                return Err(AnalyticError::CoefficientMismatch { index });
            }
            if coefficient.is_zero() {
                return Err(AnalyticError::ZeroCoefficient { index });
            }
            let ratio = normalized_ratio(coefficient, &self.rho, sample, self.exponent);
            if ratio != self.ratios[index] {
                return Err(AnalyticError::RatioMismatch { index });
            }
            ratios.push(ratio);
        }

        let reference = ratios[2].clone();
        if reference.is_zero() {
            return Err(AnalyticError::ZeroCoefficient { index: 2 });
        }
        for (index, ratio) in ratios.iter().enumerate() {
            let error = (ratio / &reference - one()).abs();
            if error != self.relative_errors[index] {
                return Err(AnalyticError::RelativeErrorMismatch { index });
            }
        }
        if self.relative_errors[0] < self.relative_errors[1] {
            return Err(AnalyticError::ErrorsDoNotShrink { index: 1 });
        }
        if self.relative_errors[1] < self.relative_errors[2] {
            return Err(AnalyticError::ErrorsDoNotShrink { index: 2 });
        }
        if !self.relative_errors[2].is_zero() {
            return Err(AnalyticError::ErrorsDoNotShrink { index: 2 });
        }
        if self.relative_errors[0] > self.tolerance {
            return Err(AnalyticError::ToleranceExceeded);
        }
        Ok(())
    }
}

fn normalized_ratio(
    coefficient: &BigRational,
    rho: &BigRational,
    sample: usize,
    exponent: u32,
) -> BigRational {
    let mut power = one();
    let mut base = rho.clone();
    let mut remaining = sample;
    while remaining > 0 {
        if remaining % 2 == 1 {
            power *= &base;
        }
        base = &base * &base;
        remaining /= 2;
    }
    let scale = BigRational::from_integer(BigInt::from(sample))
        .pow(i32::try_from(exponent).unwrap_or(i32::MAX));
    coefficient * power / scale
}

/// One less than the largest multiplicity among the factors whose modulus
/// polynomial has the radius as a root.
///
/// Dominance is decided the same way `verify` decides everything else: for an
/// exact rational radius by evaluating `g` there, and for an algebraic one by a
/// sign change of `g`'s square-free part across the refined bracket — which,
/// given that the global product has exactly one root in the coarse bracket, can
/// only be the radius.
fn dominant_exponent(certificate: &RadiusCertificate) -> Result<u32, AnalyticError> {
    let mut best: Option<u32> = None;
    for bound in &certificate.factors {
        let dominant = match &certificate.radius {
            RadiusOfConvergence::Exact(value) => {
                poly_eval(&bound.modulus_polynomial, value).is_zero()
            }
            RadiusOfConvergence::Algebraic(data) => {
                let squarefree = poly_squarefree(&bound.modulus_polynomial);
                let at_lower = poly_eval(&squarefree, &data.lower);
                let at_upper = poly_eval(&squarefree, &data.upper);
                (at_lower * at_upper).is_negative()
            }
            RadiusOfConvergence::Infinite | RadiusOfConvergence::LowerBound(_) => {
                return Err(AnalyticError::RadiusNotExact);
            }
        };
        if dominant {
            best = Some(best.map_or(bound.multiplicity, |m| m.max(bound.multiplicity)));
        }
    }
    match best {
        Some(multiplicity) if multiplicity >= 1 => Ok(multiplicity - 1),
        _ => Err(AnalyticError::NoDominantFactor),
    }
}

/// Sampled coefficient asymptotics for `numerator / denominator`, at
/// `n = base, 2·base, 4·base`.
///
/// The result is labelled **`asymptotic-verified-at-finite-n`** — see
/// [`CoefficientAsymptotics`] for exactly what that does and does not claim.
///
/// # Errors
///
/// Declines when the radius is only bounded, when a sampled coefficient is zero
/// (which is where a function with several dominant singularities lands —
/// `1/(1+x²)`, whose coefficients oscillate `1, 0, −1, 0, …`, has no `C·nᵏ·ρ⁻ⁿ`
/// form to sample), when the sampled errors do not shrink, or when the coarsest
/// sample's relative error is still above the tolerance — for which the remedy
/// is a larger `base`, and the decline carries the error it measured so the
/// caller can see how much larger.
pub fn coefficient_asymptotics(
    numerator: &[BigRational],
    denominator: &[BigRational],
    base: usize,
) -> Result<CoefficientAsymptotics, AnalyticDecline> {
    if base < 4 {
        return Err(AnalyticDecline::SampleTooSmall);
    }
    let radius = radius_of_convergence(numerator, denominator)?;
    let (bracket_lower, bracket_upper) = radius
        .radius
        .bracket()
        .ok_or(AnalyticDecline::RadiusNotExact)?;
    let rho = (&bracket_lower + &bracket_upper) / int(2);
    let exponent = dominant_exponent(&radius).map_err(|error| match error {
        AnalyticError::NoDominantFactor => AnalyticDecline::NoDominantFactor,
        other => AnalyticDecline::CertificateRefused(other),
    })?;

    let samples = vec![base, 2 * base, 4 * base];
    let (series, _) = FormalPowerSeries::from_rational_function(numerator, denominator, samples[2])
        .ok_or(AnalyticDecline::SeriesDeclined)?;

    let mut coefficients = Vec::with_capacity(3);
    let mut ratios = Vec::with_capacity(3);
    for (index, &sample) in samples.iter().enumerate() {
        let coefficient = series
            .coefficient(sample)
            .ok_or(AnalyticDecline::SeriesDeclined)?
            .clone();
        if coefficient.is_zero() {
            return Err(AnalyticDecline::ZeroCoefficient { index });
        }
        ratios.push(normalized_ratio(&coefficient, &rho, sample, exponent));
        coefficients.push(coefficient);
    }

    let reference = ratios[2].clone();
    if reference.is_zero() {
        return Err(AnalyticDecline::ZeroCoefficient { index: 2 });
    }
    let relative_errors: Vec<BigRational> = ratios
        .iter()
        .map(|ratio| (ratio / &reference - one()).abs())
        .collect();
    if relative_errors[0] < relative_errors[1] || relative_errors[1] < relative_errors[2] {
        return Err(AnalyticDecline::ErrorsDoNotShrink);
    }
    let tolerance = tolerance_cap();
    if relative_errors[0] > tolerance {
        return Err(AnalyticDecline::ToleranceExceeded {
            error: relative_errors[0].clone(),
        });
    }

    let certificate = CoefficientAsymptotics {
        numerator: poly_trim(numerator.to_vec()),
        denominator: poly_trim(denominator.to_vec()),
        radius,
        rho,
        exponent,
        samples,
        coefficients,
        ratios,
        relative_errors,
        tolerance,
    };
    certificate
        .verify()
        .map_err(AnalyticDecline::CertificateRefused)?;
    Ok(certificate)
}

#[cfg(test)]
mod tests {
    use super::{
        AlgebraicRadius, AnalyticDecline, AnalyticError, FactorModulusBound, ModulusRoute,
        RadiusCertificate, RadiusOfConvergence, accept_pairwise_resultant, coefficient_asymptotics,
        count_roots_in, pairwise_product_resultant, poly_trim, radius_of_convergence,
        resultant_modulus_polynomial,
    };
    use axeyum_ir::Rational;
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
        values.iter().map(|&v| r(v)).collect()
    }

    // -- radius, exact rational -------------------------------------------
    #[test]
    fn radius_of_one_over_one_minus_x_is_exactly_one() {
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, -1])).unwrap();
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(r(1)));
        assert_eq!(certificate.factors.len(), 1);
        assert_eq!(certificate.factors[0].route, ModulusRoute::AllRealRoots);
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn radius_of_one_over_one_minus_three_x_is_exactly_one_third() {
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, -3])).unwrap();
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(q(1, 3)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn radius_of_one_over_one_plus_x_squared_is_exactly_one_via_the_conjugate_pair_route() {
        // The case the first slice named as the reason it shipped nothing: the
        // denominator has no real root at all, so a real-roots-only bound is
        // wrong here.
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, 0, 1])).unwrap();
        assert_eq!(certificate.factors.len(), 1);
        assert_eq!(certificate.factors[0].route, ModulusRoute::ConjugatePair);
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(r(1)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn radius_of_one_over_two_plus_x_squared_is_the_irrational_square_root_of_two() {
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[2, 0, 1])).unwrap();
        assert_eq!(certificate.factors[0].route, ModulusRoute::ConjugatePair);
        let (lower, upper) = certificate.radius.bracket().unwrap();
        assert!(lower < upper);
        // √2 = 1.41421356…
        assert!(lower > q(141_421_356, 100_000_000));
        assert!(upper < q(141_421_357, 100_000_000));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn radius_of_the_fibonacci_generating_function_is_the_reciprocal_golden_ratio() {
        // 1/(1 − x − x²). The denominator's roots are real but irrational, so
        // the answer is algebraic: the smallest positive root of
        // g(t) = (1 − t − t²)(1 + t − t²) = 1 − 3t² + t⁴.
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, -1, -1])).unwrap();
        assert_eq!(certificate.factors[0].route, ModulusRoute::AllRealRoots);
        let RadiusOfConvergence::Algebraic(ref data) = certificate.radius else {
            panic!("expected an algebraic radius, got {:?}", certificate.radius);
        };
        let AlgebraicRadius {
            ref polynomial,
            ref lower,
            ref upper,
            ..
        } = **data;
        assert_eq!(*polynomial, rats(&[1, 0, -3, 0, 1]));
        // 1/φ = 0.6180339887498948…
        assert!(*lower > q(6_180_339_887, 10_000_000_000));
        assert!(*upper < q(6_180_339_888, 10_000_000_000));
        assert_eq!(certificate.verify(), Ok(()));
    }

    // -- radius, the pairwise-product resultant route ----------------------

    #[test]
    fn radius_of_the_fifth_cyclotomic_denominator_is_exactly_one_via_the_pairwise_resultant() {
        // `1 + x + x² + x³ + x⁴` is irreducible with all four roots on the unit
        // circle. Neither wave-two route reaches it — no real root at all, and
        // degree 4 is past the conjugate-pair shape — so wave two answered with
        // the reciprocal Cauchy bound 1/2 where the truth is 1. The
        // pairwise-product resultant gives the 1 exactly.
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, 1, 1, 1, 1])).unwrap();
        assert_eq!(certificate.factors.len(), 1);
        assert_eq!(
            certificate.factors[0].route,
            ModulusRoute::PairwiseResultant
        );
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(r(1)));
        // g(t) = (t−1)⁴·Φ₅(t)³ has square-free part t⁵ − 1, so the modulus
        // polynomial is t¹⁰ − 1 and not the degree-32 substitution of g itself.
        let mut expected = vec![r(0); 11];
        expected[0] = r(-1);
        expected[10] = r(1);
        assert_eq!(certificate.factors[0].modulus_polynomial, expected);
        assert_eq!(certificate.verify(), Ok(()));
        assert_eq!(certificate.radius.bracket(), Some((r(1), r(1))));
    }

    #[test]
    fn radius_of_one_over_one_plus_x_cubed_is_exactly_one() {
        // `1 + x³` has one real root (−1) and a conjugate pair of modulus 1, and
        // it splits over ℚ into `(1 + x)(1 − x + x²)`, so the two wave-two routes
        // between them still reach it.
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, 0, 0, 1])).unwrap();
        assert_eq!(
            certificate
                .factors
                .iter()
                .map(|bound| bound.route)
                .collect::<Vec<_>>(),
            vec![ModulusRoute::AllRealRoots, ModulusRoute::ConjugatePair]
        );
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(r(1)));
        assert_eq!(certificate.verify(), Ok(()));

        // The new route reaches the *unfactored* cubic on its own, and agrees.
        // Its modulus polynomial has 1 as its smallest positive root.
        let modulus = resultant_modulus_polynomial(&rats(&[1, 0, 0, 1])).unwrap();
        assert_eq!(count_roots_in(&modulus, &r(0), &r(1)), Some(1));
        assert!(super::poly_eval(&modulus, &r(1)).is_zero());
    }

    #[test]
    fn radius_of_one_over_one_minus_x_minus_x_cubed_is_the_real_root_of_x_cubed_plus_x_minus_one() {
        // `1 − x − x³` is irreducible over ℚ (neither ±1 is a root, and a cubic
        // with no rational root is irreducible) with ONE real root and one
        // conjugate pair. `1 − x − x³ = 0` ⇔ `x³ + x − 1 = 0`, so the real
        // singularity is ρ = 0.6823278038…, the real root of `x³ + x − 1`. The
        // three roots multiply to 1, so the pair has |w|² = 1/ρ and
        // |w| ≈ 1.2106: **the real root is the dominant singularity** and the
        // complex pair is strictly farther out. Wave two could say only that the
        // radius was at least 1/2.
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, -1, 0, -1])).unwrap();
        assert_eq!(certificate.factors.len(), 1);
        assert_eq!(
            certificate.factors[0].route,
            ModulusRoute::PairwiseResultant
        );
        let RadiusOfConvergence::Algebraic(ref data) = certificate.radius else {
            panic!("expected an algebraic radius, got {:?}", certificate.radius);
        };
        // Nine pairwise products collapse to six distinct ones, so g's
        // square-free part has degree 6 and the modulus polynomial degree 12.
        assert_eq!(data.polynomial.len() - 1, 12);
        // ρ = 0.68232780382801932…
        assert!(data.lower > q(68_232_780_382_801, 100_000_000_000_000));
        assert!(data.upper < q(68_232_780_382_802, 100_000_000_000_000));
        assert_eq!(certificate.verify(), Ok(()));

        // Exactly one modulus at or below 1 (the real root) and exactly one
        // above it (the conjugate pair): the dominance claim, as a root count.
        let modulus = &certificate.factors[0].modulus_polynomial;
        assert_eq!(count_roots_in(modulus, &r(0), &r(1)), Some(1));
        assert_eq!(count_roots_in(modulus, &r(1), &r(2)), Some(1));
        assert_eq!(count_roots_in(modulus, &q(6, 5), &q(61, 50)), Some(1));
    }

    #[test]
    fn radius_of_two_minus_x_squared_times_the_third_cyclotomic_is_exactly_one() {
        // (2 − x²)(1 + x + x²): moduli √2 (real pair) and 1 (conjugate pair).
        // The minimum is 1, so the composed answer is exactly 1 and the √2
        // factor is not the dominant singularity.
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[2, 2, 1, -1, -1])).unwrap();
        assert_eq!(
            certificate
                .factors
                .iter()
                .map(|bound| bound.route)
                .collect::<Vec<_>>(),
            vec![ModulusRoute::AllRealRoots, ModulusRoute::ConjugatePair]
        );
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(r(1)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn radius_of_a_resultant_factor_composed_with_a_linear_one_takes_the_smaller_modulus() {
        // (1 − x − x³)(1 − 3x) = 1 − 4x + 3x² − x³ + 3x⁴. The linear factor's
        // pole at 1/3 is nearer than the cubic's 0.6823…, so the composed
        // radius is exactly 1/3 — a rational answer reached with one factor on
        // the new route and one on a wave-two route.
        let certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, -4, 3, -1, 3])).unwrap();
        assert_eq!(
            certificate
                .factors
                .iter()
                .map(|bound| bound.route)
                .collect::<Vec<_>>(),
            vec![ModulusRoute::AllRealRoots, ModulusRoute::PairwiseResultant]
        );
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(q(1, 3)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn radius_of_the_seventh_cyclotomic_denominator_stays_a_lower_bound_above_the_degree_cap() {
        // Φ₇ = 1 + x + … + x⁶ is irreducible of degree 6, and 6 is above
        // MAX_RESULTANT_FACTOR_DEGREE, so the new route declines by policy and
        // the reciprocal Cauchy bound 1/2 remains — with the degree, not the
        // mathematics, as the stated reason. This is now the ONLY way a factor
        // reaches the lower-bound label.
        let certificate =
            radius_of_convergence(&rats(&[1]), &rats(&[1, 1, 1, 1, 1, 1, 1])).unwrap();
        assert_eq!(certificate.factors.len(), 1);
        assert_eq!(certificate.factors[0].route, ModulusRoute::ReciprocalCauchy);
        assert_eq!(certificate.radius, RadiusOfConvergence::LowerBound(q(1, 2)));
        assert!(certificate.radius.bracket().is_none());
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn the_pairwise_resultant_of_a_linear_factor_is_the_square_of_its_root() {
        // f = 1 − 3x has the single root 1/3, so g(t) = t − 1/9 and the modulus
        // polynomial is t² − 1/9. The smallest hand-checkable case of the
        // construction, computed by the same code path as the quartic.
        let resultant = pairwise_product_resultant(&rats(&[1, -3])).unwrap();
        assert_eq!(resultant, vec![q(-1, 9), r(1)]);
        let modulus = resultant_modulus_polynomial(&rats(&[1, -3])).unwrap();
        assert_eq!(modulus, vec![q(-1, 9), r(0), r(1)]);
    }

    #[test]
    fn a_spurious_pairwise_product_is_never_the_smallest_positive_root() {
        // f = 4 − 5x + x² has roots 1 and 4. The pairwise products are
        // 1, 4, 4, 16, so g has the positive root 4 — which is NOT |rᵢ|² for
        // any i — and the modulus polynomial g(t²) has the positive root 2,
        // a spurious modulus. The theorem says every product has modulus at
        // least (min|r|)², so the spurious root can only sit ABOVE the answer:
        // the smallest positive root is still 1.
        let modulus = resultant_modulus_polynomial(&rats(&[4, -5, 1])).unwrap();
        assert_eq!(count_roots_in(&modulus, &r(0), &r(1)), Some(1));
        assert_eq!(count_roots_in(&modulus, &r(0), &r(2)), Some(2));
        assert_eq!(count_roots_in(&modulus, &r(0), &r(4)), Some(3));
    }

    /// The certificate for `1/(4 − 5x + x²)` re-expressed with the quadratic
    /// kept whole and put on the pairwise-product route, so the spurious-root
    /// forgeries below have a certificate to attack. The producer splits it into
    /// two linear factors and takes the cheaper all-real-roots route; nothing in
    /// the certificate's contract requires the factors to be irreducible, and
    /// `verify` re-multiplies whatever factorization it is handed.
    fn spurious_product_certificate() -> RadiusCertificate {
        let denominator = rats(&[4, -5, 1]);
        let mut certificate = radius_of_convergence(&rats(&[1]), &denominator).unwrap();
        certificate.content = r(1);
        certificate.factors = vec![FactorModulusBound {
            factor: denominator.clone(),
            multiplicity: 1,
            route: ModulusRoute::PairwiseResultant,
            modulus_polynomial: resultant_modulus_polynomial(&denominator).unwrap(),
            lower: q(4, 9),
        }];
        certificate
    }

    #[test]
    fn the_pairwise_route_agrees_with_the_all_real_roots_route_on_a_shared_factor() {
        let certificate = spurious_product_certificate();
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(r(1)));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn forged_spurious_pairwise_product_claimed_as_the_radius_is_refused() {
        // 2 = √(1·4) is a positive root of the modulus polynomial but not a
        // modulus. Claiming it is caught by the root count, not by taste.
        let mut certificate = spurious_product_certificate();
        certificate.radius = RadiusOfConvergence::Exact(r(2));
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::RootCountMismatch {
                expected: 1,
                found: 2
            })
        );
    }

    #[test]
    fn forged_pairwise_resultant_modulus_polynomial_is_refused() {
        let mut certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, 1, 1, 1, 1])).unwrap();
        // t¹⁰ − 1 replaced by t¹⁰ − 2: still degree 10, still monic, but not the
        // polynomial the route defines.
        certificate.factors[0].modulus_polynomial[0] = r(-2);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::ModulusPolynomialMismatch { factor: 0 })
        );
    }

    #[test]
    fn forged_pairwise_route_above_the_degree_cap_is_refused() {
        let mut certificate =
            radius_of_convergence(&rats(&[1]), &rats(&[1, 1, 1, 1, 1, 1, 1])).unwrap();
        certificate.factors[0].route = ModulusRoute::PairwiseResultant;
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::RouteNotApplicable { factor: 0 })
        );
    }

    #[test]
    fn forged_pairwise_resultant_lower_bound_above_the_smallest_modulus_is_refused() {
        let mut certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, 1, 1, 1, 1])).unwrap();
        certificate.factors[0].lower = r(2);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::LowerBoundNotCertified { factor: 0 })
        );
    }

    #[test]
    fn a_resultant_of_the_wrong_degree_is_refused_by_the_self_check() {
        // The determinant must have degree n² = 16 for Φ₅. A degree-15 one is
        // not the resultant, whatever else is true of it.
        let factor = rats(&[1, 1, 1, 1, 1]);
        let honest = pairwise_product_resultant(&factor).unwrap();
        assert_eq!(honest.len() - 1, 16);
        assert!(accept_pairwise_resultant(&factor, &honest).is_some());
        let truncated = poly_trim(honest[..16].to_vec());
        assert_eq!(accept_pairwise_resultant(&factor, &truncated), None);
    }

    #[test]
    fn a_resultant_with_the_wrong_constant_term_is_refused_by_the_self_check() {
        // g(0) = (−1)ⁿ (a₀/aₙ)^{2n} is an exact consequence of the product form
        // and is NOT how the determinant is computed, so it is an independent
        // check on the primitive. Φ₅ is monic with a₀ = 1 and n = 4, so
        // g(0) = 1; anything else is a corrupted determinant.
        let factor = rats(&[1, 1, 1, 1, 1]);
        let honest = pairwise_product_resultant(&factor).unwrap();
        assert_eq!(honest[0], r(1));
        let mut corrupted = honest.clone();
        corrupted[0] = r(2);
        assert_eq!(accept_pairwise_resultant(&factor, &corrupted), None);
    }

    #[test]
    fn bignum_and_machine_sturm_counts_agree() {
        // The bignum chain is a fallback for degrees the `i128` reuse cannot
        // hold. Where both widths answer, they must answer the same — otherwise
        // the fallback is an unchecked second opinion.
        let polynomials = [
            rats(&[1, -1]),
            rats(&[1, 0, 1]),
            rats(&[1, -1, -1]),
            rats(&[1, 0, -3, 0, 1]),
            rats(&[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
            rats(&[4, -5, 1]),
            rats(&[2, -3, 1]),
            rats(&[-6, 11, -6, 1]),
            rats(&[1, 1, 1, 1, 1]),
        ];
        let points = [
            q(0, 1),
            q(1, 4),
            q(1, 3),
            q(1, 2),
            q(1, 1),
            q(3, 2),
            q(5, 1),
        ];
        let mut compared = 0usize;
        for polynomial in &polynomials {
            let machine: Vec<Rational> = polynomial
                .iter()
                .map(|c| Rational::from_big_rational(c).unwrap())
                .collect();
            let chain = super::sturm_chain_big(polynomial).unwrap();
            for window in points.windows(2) {
                let (low, high) = (&window[0], &window[1]);
                let expected = crate::sturm::count_real_roots_in(
                    &machine,
                    Rational::from_big_rational(low).unwrap(),
                    Rational::from_big_rational(high).unwrap(),
                )
                .unwrap();
                let found = super::RootCounter::count_big(&chain, low, high);
                assert_eq!(found, expected, "{polynomial:?} on ({low}, {high}]");
                compared += 1;
            }
        }
        assert_eq!(compared, 54);
    }

    #[test]
    fn radius_of_a_polynomial_is_infinite() {
        let certificate = radius_of_convergence(&rats(&[1, 2, 3]), &rats(&[2])).unwrap();
        assert_eq!(certificate.radius, RadiusOfConvergence::Infinite);
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn radius_cancels_a_common_factor_before_looking_at_the_poles() {
        // (1 − x) / ((1 − x)(1 − 2x)): the pole at x = 1 is cancelled, so the
        // radius is 1/2 and not 1. Without the gcd step this answers 1/2 anyway
        // — the point is that the Bézout witness proves nothing further cancels.
        let denominator = rats(&[1, -3, 2]); // (1−x)(1−2x)
        let certificate = radius_of_convergence(&rats(&[1, -1]), &denominator).unwrap();
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(q(1, 2)));
        assert_eq!(certificate.factors.len(), 1);
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn radius_declines_when_the_denominator_vanishes_at_the_origin() {
        assert_eq!(
            radius_of_convergence(&rats(&[1]), &rats(&[0, 1])),
            Err(AnalyticDecline::SingularAtZero)
        );
    }

    #[test]
    fn radius_declines_on_an_empty_denominator() {
        assert_eq!(
            radius_of_convergence(&rats(&[1]), &[]),
            Err(AnalyticDecline::EmptyDenominator)
        );
    }

    // -- radius, forged certificates ---------------------------------------

    fn fibonacci_radius() -> RadiusCertificate {
        radius_of_convergence(&rats(&[1]), &rats(&[1, -1, -1])).unwrap()
    }

    #[test]
    fn forged_exact_radius_below_the_true_smallest_modulus_is_refused() {
        let mut certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, -1])).unwrap();
        certificate.radius = RadiusOfConvergence::Exact(q(1, 2));
        assert_eq!(certificate.verify(), Err(AnalyticError::NotARoot));
    }

    #[test]
    fn forged_exact_radius_at_a_larger_root_is_refused_by_the_root_count() {
        // g(t) = 1 − t² for 1/(1−x): t = −1 is a root but not the smallest
        // positive one, and t = 1 is. Claiming the Cauchy bound instead is
        // caught because it is not a root at all, so use a genuine larger root
        // of a two-factor product: (1−x)(1−x/2) has moduli 1 and 2.
        let denominator = rats(&[2, -3, 1]); // 2 − 3x + x² = (1−x)(2−x)
        let mut certificate = radius_of_convergence(&rats(&[1]), &denominator).unwrap();
        assert_eq!(certificate.radius, RadiusOfConvergence::Exact(r(1)));
        certificate.radius = RadiusOfConvergence::Exact(r(2));
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::RootCountMismatch {
                expected: 1,
                found: 2
            })
        );
    }

    #[test]
    fn forged_factorization_content_is_refused() {
        let mut certificate = fibonacci_radius();
        certificate.content = r(7);
        assert!(matches!(
            certificate.verify(),
            Err(AnalyticError::FactorProductMismatch { .. })
        ));
    }

    #[test]
    fn forged_common_factor_is_refused_by_the_numerator_split() {
        let mut certificate = fibonacci_radius();
        certificate.common_factor = rats(&[2]);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::NumeratorSplitMismatch { degree: 0 })
        );
    }

    #[test]
    fn forged_reduced_denominator_that_does_not_multiply_back_is_refused() {
        // The numerator split still holds, so this reaches the denominator
        // guard and nothing else. Without a case that isolates it the guard was
        // dead weight: its mutation control survived until this test existed.
        let mut certificate = fibonacci_radius();
        certificate.reduced_denominator = rats(&[1, -1, -2]);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::DenominatorSplitMismatch { degree: 2 })
        );
    }

    #[test]
    fn forged_bezout_pair_is_refused_as_not_coprime() {
        let mut certificate = fibonacci_radius();
        certificate.bezout_numerator = rats(&[0]);
        certificate.bezout_denominator = rats(&[0]);
        assert_eq!(certificate.verify(), Err(AnalyticError::NotCoprime));
    }

    #[test]
    fn forged_all_real_roots_route_on_a_complex_rooted_factor_is_refused() {
        let mut certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, 0, 1])).unwrap();
        certificate.factors[0].route = ModulusRoute::AllRealRoots;
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::RouteNotApplicable { factor: 0 })
        );
    }

    #[test]
    fn forged_modulus_polynomial_is_refused() {
        let mut certificate = fibonacci_radius();
        certificate.factors[0].modulus_polynomial = rats(&[1, 0, -2, 0, 1]);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::ModulusPolynomialMismatch { factor: 0 })
        );
    }

    #[test]
    fn forged_factor_lower_bound_above_a_real_root_is_refused() {
        let mut certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, -1])).unwrap();
        certificate.factors[0].lower = r(2);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::LowerBoundNotCertified { factor: 0 })
        );
    }

    #[test]
    fn forged_conjugate_pair_lower_bound_above_the_modulus_is_refused() {
        let mut certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, 0, 1])).unwrap();
        certificate.factors[0].lower = r(2);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::LowerBoundNotCertified { factor: 0 })
        );
    }

    #[test]
    fn forged_global_lower_bound_above_a_factor_bound_is_refused() {
        let mut certificate =
            radius_of_convergence(&rats(&[1]), &rats(&[1, 1, 1, 1, 1, 1, 1])).unwrap();
        certificate.radius = RadiusOfConvergence::LowerBound(r(3));
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::LowerBoundExceedsFactor { factor: 0 })
        );
    }

    #[test]
    fn forged_exact_radius_over_a_bound_only_factor_is_refused() {
        let mut certificate =
            radius_of_convergence(&rats(&[1]), &rats(&[1, 1, 1, 1, 1, 1, 1])).unwrap();
        certificate.radius = RadiusOfConvergence::Exact(r(1));
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::InexactRoute { factor: 0 })
        );
    }

    #[test]
    fn forged_global_modulus_polynomial_is_refused() {
        let mut certificate = fibonacci_radius();
        if let RadiusOfConvergence::Algebraic(ref mut data) = certificate.radius {
            data.polynomial = rats(&[1, 0, -4, 0, 1]);
        }
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::GlobalModulusMismatch)
        );
    }

    #[test]
    fn forged_refined_bracket_outside_the_coarse_one_is_refused() {
        let mut certificate = fibonacci_radius();
        if let RadiusOfConvergence::Algebraic(ref mut data) = certificate.radius {
            data.upper = &data.coarse_upper + r(1);
        }
        assert_eq!(certificate.verify(), Err(AnalyticError::MalformedBracket));
    }

    #[test]
    fn forged_refined_bracket_without_a_sign_change_is_refused() {
        let mut certificate = fibonacci_radius();
        if let RadiusOfConvergence::Algebraic(ref mut data) = certificate.radius {
            // A sub-interval of the coarse bracket that sits entirely left of
            // the root: well formed, but it traps nothing.
            data.lower = data.coarse_lower.clone();
            data.upper = &data.coarse_lower + q(1, 1_000_000);
        }
        assert_eq!(certificate.verify(), Err(AnalyticError::NoSignChange));
    }

    #[test]
    fn forged_infinite_radius_over_a_real_pole_is_refused() {
        let mut certificate = radius_of_convergence(&rats(&[1]), &rats(&[1, -1])).unwrap();
        certificate.radius = RadiusOfConvergence::Infinite;
        assert_eq!(certificate.verify(), Err(AnalyticError::RadiusNotExact));
    }

    #[test]
    fn forged_factor_vanishing_at_the_origin_is_refused() {
        let mut certificate = fibonacci_radius();
        certificate.factors.push(FactorModulusBound {
            factor: rats(&[0, 1]),
            multiplicity: 1,
            route: ModulusRoute::AllRealRoots,
            modulus_polynomial: rats(&[0, 0, -1]),
            lower: q(1, 2),
        });
        assert!(matches!(
            certificate.verify(),
            Err(AnalyticError::FactorProductMismatch { .. }
                | AnalyticError::FactorVanishesAtZero { factor: 1 })
        ));
    }

    // -- coefficient asymptotics -------------------------------------------

    #[test]
    fn fibonacci_growth_rate_is_the_golden_ratio() {
        let certificate = coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, -1]), 20).unwrap();
        assert_eq!(certificate.exponent, 0);
        // 1/ρ = φ = 1.61803398874989…
        let reciprocal = BigRational::from_integer(BigInt::from(1)) / &certificate.rho;
        assert!(reciprocal > q(1_618_033_988, 1_000_000_000));
        assert!(reciprocal < q(1_618_033_989, 1_000_000_000));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn fibonacci_relative_errors_shrink_along_the_three_samples() {
        let certificate = coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, -1]), 20).unwrap();
        assert!(certificate.relative_errors[0] > certificate.relative_errors[1]);
        assert!(certificate.relative_errors[1] > certificate.relative_errors[2]);
        assert_eq!(certificate.relative_errors[2], r(0));
        assert_eq!(certificate.samples, vec![20, 40, 80]);
    }

    #[test]
    fn one_over_one_minus_x_squared_grows_linearly() {
        // 1/(1−x)² has a(n) = n+1: exponent 1 from the double pole.
        let certificate = coefficient_asymptotics(&rats(&[1]), &rats(&[1, -2, 1]), 100).unwrap();
        assert_eq!(certificate.exponent, 1);
        assert_eq!(certificate.rho, r(1));
        assert_eq!(certificate.coefficients[0], r(101));
        assert_eq!(certificate.coefficients[2], r(401));
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn one_over_one_minus_x_has_constant_growth() {
        let certificate = coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1]), 8).unwrap();
        assert_eq!(certificate.exponent, 0);
        assert_eq!(certificate.rho, r(1));
        assert_eq!(certificate.relative_errors, vec![r(0), r(0), r(0)]);
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn asymptotics_decline_on_the_oscillating_denominator_one_plus_x_squared() {
        // a(n) = 1, 0, −1, 0, … has no C·nᵏ·ρ⁻ⁿ form; the zero coefficients are
        // where the route stops.
        assert_eq!(
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, 0, 1]), 5),
            Err(AnalyticDecline::ZeroCoefficient { index: 0 })
        );
    }

    #[test]
    fn asymptotics_decline_when_the_radius_is_only_bounded() {
        // Φ₇ is above the resultant route's degree cap, so its radius is still
        // a bound and the asymptotics stop before they sample anything. Φ₅ used
        // to land here; it now reaches an exact radius and stops one guard later.
        assert_eq!(
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, 1, 1, 1, 1, 1, 1]), 8),
            Err(AnalyticDecline::RadiusNotExact)
        );
    }

    #[test]
    fn asymptotics_on_the_fifth_cyclotomic_now_pass_the_radius_and_stop_at_a_zero_coefficient() {
        // 1/Φ₅ = (1 − x)/(1 − x⁵) has coefficients 1, −1, 0, 0, 0, 1, −1, …, so
        // there is no C·nᵏ·ρ⁻ⁿ form to sample. What changed in wave three is
        // WHICH guard stops it: the radius is now exactly 1 and the route gets
        // as far as the coefficients before declining.
        assert_eq!(
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, 1, 1, 1, 1]), 8),
            Err(AnalyticDecline::ZeroCoefficient { index: 0 })
        );
    }

    #[test]
    fn growth_rate_of_one_over_one_minus_x_minus_x_cubed_uses_the_exact_resultant_radius() {
        // a(n) = a(n−1) + a(n−3) grows like C·ρ⁻ⁿ with ρ the real root of
        // x³ + x − 1. Wave two could not run this at all: the radius was only
        // bounded, and `coefficient_asymptotics` refuses a bounded radius.
        let certificate = coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, 0, -1]), 20).unwrap();
        assert_eq!(certificate.exponent, 0);
        assert_eq!(
            certificate.radius.factors[0].route,
            ModulusRoute::PairwiseResultant
        );
        assert!(certificate.rho > q(68_232_780_382_801, 100_000_000_000_000));
        assert!(certificate.rho < q(68_232_780_382_803, 100_000_000_000_000));
        assert!(certificate.relative_errors[0] > certificate.relative_errors[1]);
        assert_eq!(certificate.verify(), Ok(()));
    }

    #[test]
    fn asymptotics_decline_when_the_sample_is_too_coarse_for_the_tolerance() {
        // The double pole's 1/n correction needs a larger base than this.
        assert!(matches!(
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, -2, 1]), 8),
            Err(AnalyticDecline::ToleranceExceeded { .. })
        ));
    }

    #[test]
    fn forged_rho_outside_the_radius_bracket_is_refused() {
        let mut certificate =
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, -1]), 20).unwrap();
        certificate.rho = q(1, 2);
        assert_eq!(certificate.verify(), Err(AnalyticError::RhoOutsideBracket));
    }

    #[test]
    fn forged_growth_exponent_is_refused() {
        let mut certificate =
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, -2, 1]), 100).unwrap();
        certificate.exponent = 0;
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::ExponentMismatch {
                declared: 0,
                derived: 1
            })
        );
    }

    #[test]
    fn forged_coefficient_is_refused() {
        let mut certificate =
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, -1]), 20).unwrap();
        certificate.coefficients[1] = r(0);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::CoefficientMismatch { index: 1 })
        );
    }

    #[test]
    fn forged_tolerance_wider_than_the_cap_is_refused() {
        let mut certificate =
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, -1]), 20).unwrap();
        certificate.tolerance = r(1000);
        assert_eq!(certificate.verify(), Err(AnalyticError::ToleranceTooLoose));
    }

    #[test]
    fn forged_relative_errors_are_refused() {
        let mut certificate =
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, -1]), 20).unwrap();
        certificate.relative_errors[0] = q(1, 1000);
        assert_eq!(
            certificate.verify(),
            Err(AnalyticError::RelativeErrorMismatch { index: 0 })
        );
    }

    #[test]
    fn forged_samples_that_are_not_n_2n_4n_are_refused() {
        let mut certificate =
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, -1]), 20).unwrap();
        certificate.samples = vec![20, 30, 80];
        assert_eq!(certificate.verify(), Err(AnalyticError::MalformedSamples));
    }

    #[test]
    fn forged_asymptotics_over_a_different_function_is_refused() {
        let mut certificate =
            coefficient_asymptotics(&rats(&[1]), &rats(&[1, -1, -1]), 20).unwrap();
        certificate.numerator = rats(&[2]);
        assert_eq!(certificate.verify(), Err(AnalyticError::FunctionMismatch));
    }
}
