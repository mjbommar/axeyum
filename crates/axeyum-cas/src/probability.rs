//! Symbolic probability: named distributions with exact moments, moment
//! generating functions, and convolution of independent sums (item 9 of the
//! Next Ten in `docs/math-department/13-computer-algebra.md`).
//!
//! # What this module reuses (and does not reinvent)
//!
//! Every quantity here is produced by an **existing** certified primitive —
//! [`crate::definite_sum`], [`crate::infinite_sum`], [`crate::improper_integrate`],
//! [`crate::laplace_transform`], [`crate::prove_wz_sum`], [`crate::equal`],
//! [`crate::expand`]/[`crate::simplify`] — never a bespoke numeric check. A
//! finite-support discrete quantity is decided by enumerating its (small,
//! concrete) support, building the exact closed `CasExpr` sum, and deciding the
//! target identity with [`crate::equal`] after [`crate::expand`] (the
//! **`ExpandEqual`** route below): this is *not* a weaker check than
//! [`crate::definite_sum`]'s telescoping certificate, it is the same
//! canonical-polynomial decision procedure ([`crate::equal`]) applied directly,
//! which is the only option once the summand itself (a binomial coefficient at
//! a *fixed* `n`) has no uniform closed form in the bound variable for
//! [`crate::definite_sum`] to telescope.
//!
//! # What the machinery certifies, and what it declines (measured, not assumed)
//!
//! Every route below was probed empirically against the live crate before this
//! module was written (see the lane's scratch probes); the findings are
//! structural, not incidental bugs to route around:
//!
//! - **A symbolic coefficient inside `exp(...)` used to break every
//!   transform-style route; it no longer does.** [`crate::laplace_transform`]
//!   and the elementary `∫e^{c·x}` antiderivative both reach `to_univariate`,
//!   which needs concrete [`axeyum_ir::Rational`] coefficients, so
//!   `Exponential(λ)` only transformed for **concrete** `λ` and an mgf's own
//!   argument `t` — symbolic by definition — declined for every continuous
//!   family. Two things were missing, and both now exist:
//!   [`crate::MultiPoly::coeffs_in`] splits a polynomial on one variable while
//!   keeping the others symbolic, and [`crate::improper_integrate_conditional`]
//!   has somewhere to put the sign condition that makes the integral converge.
//!   The route builds the repeated-integration-by-parts antiderivative with the
//!   rate symbolic, **proves** it against the original integrand with
//!   [`crate::prove_derivative`], and records what the boundary assumed. That
//!   closes `Exponential(λ)` at symbolic `λ` (all four quantities) and
//!   `Uniform(a,b)`'s mgf. A condition it *can* decide it decides: a concrete
//!   rate of the right sign comes back unconditional, and one of the wrong sign
//!   — a divergent integral — declines outright.
//! - **`Σ (j+1)·p·qʲ` certifies; the earlier `k/k` report was a spelling, not a
//!   gap.** [`crate::gosper_sum`]'s *geometric* path returns a pole-free
//!   antidifference `X(k)·qᵏ` for `(j+1)·p·qʲ`, and [`crate::limit`] resolves it
//!   at `∞`; only the *rational* Gosper reconstruction carries the removable
//!   `1/p(k)` pole that was reported as an unresolvable `k/k`. Re-measured
//!   here: `Geometric`'s **mean and variance certify** for concrete `p` through
//!   [`crate::infinite_sum`] on the reindexed summand (`j = k−1`, which is what
//!   puts the geometric factor in the machinery's own `exp(j·ln q)`
//!   convention).
//! - **A *symbolic* `p` needed a whole route, not a hypothesis bolted onto the
//!   old one.** Gosper genuinely has no antidifference for a symbolic ratio
//!   (`gosper_sum(p·(1−p)ʲ, j)` and `gosper_sum(qʲ, j)` both return `None`, run
//!   rather than remembered in
//!   `the_symbolic_ratio_still_declines_in_gosper_and_is_reached_conditionally`),
//!   so there was nothing for a `SignCondition` to attach to — the earlier
//!   reading, that a hypothesis channel "would not help", was right about *that*
//!   route and wrong about the conclusion. [`crate::infinite_sum_conditional`]
//!   adds the missing one: the geometric series
//!   `Σ_{j≥0} j^{(m)}·qʲ = m!·qᵐ/(1−q)^{m+1}`, one recognized identity with the
//!   shape and the falling-factorial expansion both decided by [`crate::equal`],
//!   and `|q| < 1` recorded where it cannot be decided. All four `Geometric`
//!   quantities now certify at symbolic `p` under `0 < p < 1` (the mgf also
//!   under `t < −ln(1−p)`), while a concrete ratio is still decided on the spot
//!   — `Σ 2ʲ` declines rather than printing the continuation `−1`.
//! - **`λᵏ/k!` is not Gosper-summable — so it goes through the recognized
//!   exponential series instead.** [`crate::gosper_sum`] genuinely returns
//!   `None` (no hypergeometric antidifference exists; `eˣ`'s Taylor tail has no
//!   telescoping form), so [`crate::infinite_sum`] falls through to its
//!   exponential-series route: `∑_{k≥0} P(k)·μᵏ/k! = e^μ·∑ⱼ (Δʲ P(0)/j!)·μʲ`,
//!   resting on the single base identity `∑ k^{(j)}·μᵏ/k! = μʲ·e^μ` with **both**
//!   steps that reach it decided by [`crate::equal`] — the shape reconstruction
//!   and the falling-factorial expansion of `P`. All four `Poisson` quantities
//!   (mass, mean, variance, mgf) now certify, for symbolic `λ` and symbolic `t`
//!   alike; the mgf works because `e^{t·k}·λᵏ` is one exponential factor of rate
//!   `t + ln λ`, so `t` is never read as a polynomial coefficient. Near-miss
//!   summands (`λᵏ/(k!·(k+1))`, the misindexed `λᵏ/(k−1)!`) are refused, not
//!   read as `e^λ`.
//! - **`integrate_gaussian` no longer requires `√a` rational.** It completes the
//!   square with a symbolic `√a`, and the differentiate-and-check certificate
//!   closes because [`crate::prove_derivative`] retries under
//!   [`crate::simplify_radicals`], which now distributes an exponent over a
//!   product carrying a surd — that is what puts the erf derivative's
//!   `exp(−(√a·(x+d))²)` and the integrand's `exp(−a·x²−…)` in one atom. So
//!   `Normal(0,1)` (`σ² = 1`, `a = 1/2`) certifies total mass, mean **and**
//!   variance. An upward Gaussian (`a ≤ 0`) still declines: it is not an erf.
//! - **The `Normal` mgf does not go through an integral in `t` at all.**
//!   Measured against the live crate, `improper_integrate(e^{−x²+t·x}, −∞, ∞)`
//!   returns `None` — the symbolic linear coefficient stops the Gaussian finder
//!   just as it stops the elementary one. **Completing the square** moves `t`
//!   out of the integral instead:
//!   `t·x − (x−μ)²/(2σ²) = μt + σ²t²/2 − (x−(μ+σ²t))²/(2σ²)`, an identity
//!   [`crate::equal`] decides, leaving `∫φ_{μ+σ²t,σ²} = 1` — which is the
//!   *existing* erf certificate at a symbolic mean. So `M(t) = e^{μt+σ²t²/2}`
//!   certifies **unconditionally** for symbolic `μ` and symbolic `t`, and a
//!   non-positive `σ²` declines (at the shifted mass for `σ² < 0`, at the
//!   identity itself for `σ² = 0`, since its `2σ²` denominator vanishes).
//! - **A symbolic `σ²` needed the erf antiderivative to be built with `√a`
//!   symbolic, and two spellings to be made to meet.** `integrate_gaussian`
//!   reaches `to_univariate`, which needs a concrete rational coefficient of
//!   `x²`, so `integrate(e^{−a·x²}, x)` still returns `None` for a symbolic `a`
//!   — that measurement has not changed.
//!   [`crate::improper_integrate_conditional`] now carries a second shape past
//!   it: `C·P(x)·e^{−a·x²}` over the whole line, with the antiderivative built
//!   from the standard reduction, **proved** by [`crate::prove_derivative`], and
//!   `a > 0` recorded for the two infinite bounds. Two spelling problems had to
//!   be solved for the certificate to close at all, and both are recorded at the
//!   code: the route reads `a` back out *by division* so the reconstruction
//!   lands on the caller's own spelling of the exponent (reading it off by
//!   substitution gives `(1/2)/s` where the caller wrote `1/(2s)`, and the two
//!   `exp` atoms then never meet), and the pdf's normalizer is spelled
//!   `√a/√π` — the one form that cancels against the route's `√π/√a` without a
//!   radical rewrite this crate does not have for a symbolic radicand — with
//!   `c·c·2πσ² = 1` **decided** to confirm it is `1/√(2πσ²)`. All four `Normal`
//!   quantities now certify at symbolic `σ²` under `σ² > 0`, and the field is a
//!   [`CasExpr`]; a concrete `σ²` still goes through the unchanged
//!   [`crate::improper_integrate`] path and stays unconditional.
//! - **The Poisson⊕Poisson convolution identity has its own, independent
//!   certificate** from [`crate::prove_wz_sum`], the Wilf–Zeilberger prover:
//!   `Σⱼ C(k,j)·λ₁ʲ·λ₂ᵏ⁻ʲ = (λ₁+λ₂)ᵏ` for *every* `k`, proved symbolically in
//!   `k` for concrete `λ₁, λ₂`. It is a different machine from the exponential
//!   series `Poisson::total_mass` now uses, so the two are genuine cross-checks
//!   rather than one route reported twice.
//!
//! # Trust model
//!
//! Every quantity returns a [`Certificate`]: a claim (`CasExpr`), the
//! [`Route`] that produced it, and a [`Trust`] tag. [`Trust::Certified`] means
//! an independent primitive (never a numeric spot-check, never `f64`) decided
//! the identity **unconditionally**. [`Trust::CertifiedUnder`] means the same
//! primitive decided it, but only under the recorded [`crate::SignCondition`]s
//! on the symbolic parameters. [`Trust::Uncertified`] carries the specific
//! reason the route declined — never silently promoted to either of the other
//! two.
//!
//! A conditional certificate is **not** a weaker unconditional one; it
//! certifies a different, smaller statement, and the condition is part of it.
//! `λ/(λ−t)` is not approximately the mgf of `Exponential(λ)` at `t ≥ λ` —
//! there is no mgf there at all, the defining integral diverges. So
//! [`Certificate::is_certified`] keeps meaning *unconditional* (every existing
//! caller gates on it), [`Certificate::is_decided`] covers both, and the
//! conditions propagate into derived claims: [`chebyshev_bound`] and
//! [`markov_bound`] carry the union of their inputs' conditions.
//!
//! Each type's `verify_*` method independently re-derives the claim from the
//! distribution's definition and re-decides equality with [`crate::equal`]. The
//! comparison is on the **whole trust tag**, not on "both are certified enough":
//! that is what refuses the dropped-hypothesis forgery, whose claim is
//! character-for-character the genuine one and whose condition list is empty.
//! See `forged_certificates_are_refused` for the three classical forgeries and
//! `an_mgf_certificate_with_the_hypothesis_dropped_is_refused` for this one.
//!
//! # What changed, wave three (symbolic-parameter continuous families)
//!
//! | quantity | before | after | hypothesis |
//! |---|---|---|---|
//! | `Exponential(λ)` mass, symbolic `λ` | uncertified (`to_univariate`) | certified | `λ > 0` |
//! | `Exponential(λ)` mean, symbolic `λ` | uncertified | certified `1/λ` | `λ > 0` |
//! | `Exponential(λ)` variance, symbolic `λ` | uncertified | certified `1/λ²` | `λ > 0` |
//! | `Exponential(λ)` mgf | uncertified (symbolic `t`) | certified `λ/(λ−t)` | `λ − t > 0` |
//! | `Uniform(a,b)` mgf | uncertified (symbolic `t`) | certified `(e^{tb}−e^{ta})/(t(b−a))` | `t ≠ 0` |
//! | `Normal(μ,σ²)` mgf, symbolic `μ`, `t` | uncertified (symbolic `t`) | certified `e^{μt+σ²t²/2}` | none (`σ²` concrete, its sign decided) |
//! | `Normal` with symbolic `σ²` | not representable | see wave four | — |
//! | `Geometric(p)`, symbolic `p` | uncertified | see wave four | — |
//!
//! `Uniform`'s `t ≠ 0` is the removable singularity of the closed form:
//! `M(0) = 1` is its limit, no route in this crate decides that limit, and so
//! the certificate does not claim it.
//!
//! # What changed, wave four (the two families that were still declining)
//!
//! | quantity | before | after | hypothesis |
//! |---|---|---|---|
//! | `Normal(μ,σ²)` mass, symbolic `σ²` | not representable | certified `1` | `σ² > 0` |
//! | `Normal(μ,σ²)` mean, symbolic `σ²` | not representable | certified `μ` | `σ² > 0` |
//! | `Normal(μ,σ²)` variance, symbolic `σ²` | not representable | certified `σ²` | `σ² > 0` |
//! | `Normal(μ,σ²)` mgf, symbolic `σ²` | not representable | certified `e^{μt+σ²t²/2}` | `σ² > 0` |
//! | `Geometric(p)` mass, symbolic `p` | uncertified | certified `1` | `0 < p < 1` |
//! | `Geometric(p)` mean, symbolic `p` | uncertified | certified `1/p` | `0 < p < 1` |
//! | `Geometric(p)` variance, symbolic `p` | uncertified | certified `(1−p)/p²` | `0 < p < 1` |
//! | `Geometric(p)` mgf, symbolic `p` and `t` | uncertified | certified `pe^t/(1−(1−p)e^t)` | `0 < p < 1` and `t < −ln(1−p)` |
//!
//! Both new hypotheses are **restated** from what the deciding route actually
//! recorded, and each restatement is guarded by an [`equal`] check that refuses
//! to relabel a condition it does not recognize: `1/(2σ²) > 0` becomes `σ² > 0`
//! only once `a·2σ² = 1` is decided, and `1 − |q| > 0` becomes `0 < p < 1` only
//! once the margin is decided to be this distribution's own. The geometric
//! restatement records conditions that **imply** what the route needed
//! (`0 < p < 1 ⟹ |1−p| < 1`) rather than restating an equivalence: a certificate
//! under a stronger hypothesis is a certificate of a smaller statement, which is
//! the reading [`Trust::CertifiedUnder`] already has, and `0 < p < 1` is the
//! parameter domain `Geometric(p)` is defined on. Recording something *weaker*
//! than the route needed would not be sound, and is exactly what the guard
//! prevents.
//!
//! What is still uncertified after wave four: a `Normal` whose variance is
//! symbolic but whose Gaussian factor is spelled differently from `e^{−(a·u²)}`
//! (an honest decline at the differentiate-and-check, not a wrong answer), a
//! `Gaussian` integrand with an uncompleted linear term in the exponent, and a
//! geometric summand with the index in a denominator or under a factorial —
//! each with its own negative control.
//!
//! Chebyshev/Markov bounds are built from certified mean/variance but are
//! **not themselves re-proved** here — [`Route::Derived`] records exactly
//! that: the inequality's soundness is inherited from probability theory, not
//! re-established by this module.

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use crate::{
    CasExpr, ConditionalIntegral, LimitPoint, SignCondition, UnaryFunc, ZeroTest,
    binomial_coefficient, definite_sum, equal, expand, improper_integrate,
    improper_integrate_conditional, infinite_sum, infinite_sum_conditional, laplace_transform,
    ntheory, prove_wz_sum, simplify,
};

/// Which existing certified primitive established a [`Certificate`]'s claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Route {
    /// Finite enumeration of a (small, concrete) support, then
    /// [`crate::expand`] and [`crate::equal`] decide the target identity
    /// directly — used when the summand (e.g. a binomial coefficient at fixed
    /// `n`) has no uniform closed form in the bound variable.
    ExpandEqual,
    /// [`crate::definite_sum`]'s telescoping certificate over a finite,
    /// symbolic-bound range.
    DefiniteSum,
    /// [`crate::infinite_sum`] over an unbounded discrete support: its
    /// telescoping-plus-limit certificate, or — for the `λᵏ/k!` family, which has
    /// no antidifference — its recognized exponential series, whose two
    /// obligations are themselves decided by [`equal`].
    InfiniteSum,
    /// [`crate::improper_integrate`]'s certified antiderivative/limit route
    /// over a continuous support.
    ImproperIntegrate,
    /// [`crate::laplace_transform`] evaluated at `s = −t`.
    LaplaceTransform,
    /// [`crate::improper_integrate_conditional`]'s symbolic-rate exponential
    /// route: the same proved antiderivative and the same fundamental theorem,
    /// with the boundary evaluation's sign conditions recorded rather than
    /// decided. Produces a [`Trust::CertifiedUnder`] whenever a parameter is
    /// symbolic — never a bare [`Trust::Certified`].
    ConditionalIntegrate,
    /// Completing the square in a Gaussian exponent, which reduces `E[e^{tX}]`
    /// to the **total mass of a shifted Normal**. Two obligations, both decided
    /// by existing machinery: the exponent identity by [`equal`], and the
    /// shifted mass by [`Continuous::total_mass`]'s own erf certificate.
    GaussianShift,
    /// The Wilf–Zeilberger prover [`crate::prove_wz_sum`]: a general
    /// (all-`k`) symbolic proof of a hypergeometric sum identity.
    WzProof,
    /// Built from already-certified inputs (e.g. mean and variance) by a
    /// formula whose own soundness is not re-derived here.
    Derived,
}

/// Whether a [`Certificate`]'s claim was independently decided, or the
/// specific reason the deciding route declined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Trust {
    /// An independent primitive decided the claim exactly, with no side
    /// condition on any parameter.
    Certified,
    /// An independent primitive decided the claim exactly, but **only under**
    /// the recorded side conditions on the symbolic parameters.
    ///
    /// This is not a weaker certificate; it is a certificate of a different,
    /// smaller statement, and the conditions are part of it. `λ/(λ−t)` is not
    /// "approximately" the mgf of `Exponential(λ)` at `t ≥ λ` — there is no mgf
    /// there at all, the defining integral diverges. So a caller that drops the
    /// conditions is asserting something false, and the `verify_*` methods
    /// refuse a certificate whose conditions differ from a fresh
    /// re-derivation's, including one that has none.
    CertifiedUnder(Vec<SignCondition>),
    /// The route declined; the claim is the standard closed form, presented
    /// for reference only. Never promoted to `Certified`.
    Uncertified(String),
}

/// A claimed quantity (total mass, a moment, an mgf, …) together with the
/// route that produced it and whether that route actually decided it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Certificate {
    /// The claimed closed form.
    pub claim: CasExpr,
    /// Which primitive produced the claim.
    pub route: Route,
    /// Whether the claim was independently decided.
    pub trust: Trust,
}

impl Certificate {
    fn certified(claim: CasExpr, route: Route) -> Self {
        Certificate {
            claim,
            route,
            trust: Trust::Certified,
        }
    }

    fn certified_under(claim: CasExpr, route: Route, hypotheses: Vec<SignCondition>) -> Self {
        debug_assert!(
            !hypotheses.is_empty(),
            "an empty condition list is an unconditional `Certified`, not a `CertifiedUnder`"
        );
        Certificate {
            claim,
            route,
            trust: Trust::CertifiedUnder(hypotheses),
        }
    }

    fn uncertified(claim: CasExpr, route: Route, reason: impl Into<String>) -> Self {
        Certificate {
            claim,
            route,
            trust: Trust::Uncertified(reason.into()),
        }
    }

    /// Whether this certificate's claim was independently decided **and needs
    /// no side condition**. A [`Trust::CertifiedUnder`] is deliberately *not*
    /// certified by this predicate: every existing caller that gates on it
    /// (the convolution and bound builders) would otherwise silently drop the
    /// conditions on the way into a derived claim.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self.trust, Trust::Certified)
    }

    /// Whether an independent primitive decided the claim, conditionally or
    /// not. Use with [`Self::hypotheses`]; a conditional claim is only true
    /// under those.
    #[must_use]
    pub fn is_decided(&self) -> bool {
        matches!(self.trust, Trust::Certified | Trust::CertifiedUnder(_))
    }

    /// The side conditions this claim rests on — empty for an unconditional
    /// [`Trust::Certified`] and for anything uncertified.
    #[must_use]
    pub fn hypotheses(&self) -> &[SignCondition] {
        match &self.trust {
            Trust::CertifiedUnder(conditions) => conditions,
            Trust::Certified | Trust::Uncertified(_) => &[],
        }
    }

    /// The side conditions rendered for a ledger row, e.g. `"lambda > 0"` or
    /// `"lambda - t > 0"`. Empty string when there are none.
    #[must_use]
    pub fn hypotheses_display(&self) -> String {
        self.hypotheses()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(" and ")
    }
}

/// Two certificates **agree**: the fresh re-derivation `a` decided its claim,
/// the presented certificate `b` carries the *same* trust tag — the same side
/// conditions, in the same order, or none on both sides — and [`crate::equal`]
/// confirms the claims are the same expression.
///
/// The trust tags are compared for equality rather than both being tested for
/// "certified enough". That is what refuses the **dropped-hypothesis forgery**:
/// a certificate claiming a bare `Trust::Certified` for `λ/(λ−t)` does not
/// agree with the re-derivation's `Trust::CertifiedUnder([λ − t > 0])`, even
/// though the *claim* is character-for-character identical. Both sides are
/// produced by the same deterministic code path, so a genuine certificate
/// always matches spelling as well as content.
fn agree(a: &Certificate, b: &Certificate) -> bool {
    a.is_decided()
        && a.trust == b.trust
        && matches!(
            equal(&a.claim, &b.claim),
            ZeroTest::Certified { equal: true, .. }
        )
}

/// Sum a finite list of `CasExpr` terms, expand, and decide the target
/// identity via [`crate::equal`] — the **`ExpandEqual`** route.
fn expand_equal_route(terms: Vec<CasExpr>, target: &CasExpr) -> Certificate {
    let mut acc = CasExpr::zero();
    for term in terms {
        acc = acc + term;
    }
    let expanded = expand(&acc).unwrap_or_else(|| acc.clone());
    let simplified = simplify(&expanded);
    match equal(&simplified, target) {
        ZeroTest::Certified { equal: true, .. } | ZeroTest::CertifiedBig { equal: true, .. } => {
            Certificate::certified(target.clone(), Route::ExpandEqual)
        }
        ZeroTest::Certified { equal: false, .. } | ZeroTest::CertifiedBig { equal: false, .. } => {
            Certificate::uncertified(
                simplified,
                Route::ExpandEqual,
                "expand+equal decided the enumerated sum does NOT equal the target",
            )
        }
        ZeroTest::Unknown => Certificate::uncertified(
            simplified,
            Route::ExpandEqual,
            "equal declined (exact-rational overflow) after expand",
        ),
    }
}

/// Whether a `CasExpr` parameter is a concrete constant (checked structurally,
/// without simplifying — a bare distribution parameter like `p` or `λ` is
/// always already `Const` or `Var` at the point this is called).
fn as_concrete(expr: &CasExpr) -> Option<Rational> {
    match expr {
        CasExpr::Const(r) => Some(*r),
        _ => None,
    }
}

/// The exact rational value of a (possibly unreduced, e.g. `Mul`/`Pow`) `CasExpr`
/// built from concrete parameters only — [`simplify`] folds it to a single
/// `Const` when every input was concrete; `None` if it does not reduce to one
/// (a symbolic parameter leaked in, or simplification declined).
fn concrete_value(expr: &CasExpr) -> Option<Rational> {
    match simplify(expr) {
        CasExpr::Const(r) => Some(r),
        _ => None,
    }
}

// ============================================================================
// Discrete distributions
// ============================================================================

/// A named discrete distribution. Parameters may be symbolic
/// ([`CasExpr::Var`]) where the certifying route tolerates it; supports that
/// must be enumerable (`Binomial`'s `n`, `DiscreteUniform`'s `a, b`) are
/// concrete by construction — there is no symbolic binomial coefficient
/// object in this crate to enumerate a symbolic-length support with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Discrete {
    /// `Bernoulli(p)`: one trial, support `{0, 1}`.
    Bernoulli(CasExpr),
    /// `Binomial(n, p)`: `n` independent Bernoulli(p) trials, support `0..=n`.
    /// `n` is concrete (no symbolic binomial coefficient object exists here).
    Binomial {
        /// Number of trials.
        n: u32,
        /// Success probability, possibly symbolic.
        p: CasExpr,
    },
    /// `Geometric(p)`: number of trials until (and including) the first
    /// success, support `1, 2, 3, …`. (Not the "failures before success"
    /// convention — chosen so `mean = 1/p`.)
    Geometric(CasExpr),
    /// `Poisson(λ)`: support `0, 1, 2, …`.
    Poisson(CasExpr),
    /// `DiscreteUniform(a, b)`: support `a..=b`, both concrete integers.
    DiscreteUniform {
        /// Lower bound (inclusive).
        a: i128,
        /// Upper bound (inclusive), `b >= a`.
        b: i128,
    },
}

impl Discrete {
    /// The probability mass at the concrete point `k` (`0` outside the
    /// support). `Poisson`'s mass is a `CasExpr` carrying the transcendental
    /// `e^{−λ}` factor, not a plain rational, even for concrete `λ`.
    #[must_use]
    pub fn pmf_at(&self, k: i128) -> CasExpr {
        match self {
            Discrete::Bernoulli(p) => match k {
                0 => CasExpr::one() - p.clone(),
                1 => p.clone(),
                _ => CasExpr::zero(),
            },
            Discrete::Binomial { n, p } => {
                if k < 0 || k > i128::from(*n) {
                    return CasExpr::zero();
                }
                #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
                let kk = k as u32;
                let coeff = ntheory::binomial(i128::from(*n), k).unwrap_or(0);
                CasExpr::Const(Rational::integer(coeff))
                    * p.clone().pow(kk)
                    * (CasExpr::one() - p.clone()).pow(*n - kk)
            }
            Discrete::Geometric(p) => {
                if k < 1 {
                    return CasExpr::zero();
                }
                #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
                let exponent = (k - 1) as u32;
                p.clone() * (CasExpr::one() - p.clone()).pow(exponent)
            }
            Discrete::Poisson(lambda) => {
                if k < 0 {
                    return CasExpr::zero();
                }
                #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
                let kk = k as u32;
                let Some(fact) = ntheory::factorial(k) else {
                    return CasExpr::zero();
                };
                (lambda.clone().pow(kk) * CasExpr::Neg(Box::new(lambda.clone())).exp())
                    / CasExpr::Const(Rational::integer(fact))
            }
            Discrete::DiscreteUniform { a, b } => {
                if k < *a || k > *b {
                    return CasExpr::zero();
                }
                CasExpr::one() / CasExpr::Const(Rational::integer(b - a + 1))
            }
        }
    }

    /// The finite-support endpoints `(lo, hi)`, or `None` for infinite
    /// support (`Geometric`, `Poisson`).
    fn finite_support(&self) -> Option<(i128, i128)> {
        match self {
            Discrete::Bernoulli(_) => Some((0, 1)),
            Discrete::Binomial { n, .. } => Some((0, i128::from(*n))),
            Discrete::DiscreteUniform { a, b } => Some((*a, *b)),
            Discrete::Geometric(_) | Discrete::Poisson(_) => None,
        }
    }

    /// `Σ_k pmf(k) = 1`, the distribution's total probability mass.
    /// # Panics
    ///
    /// Panics only on `i128` overflow building a small exact-rational constant
    /// (e.g. `(a+b)/2`); this does not occur for realistic distribution
    /// parameters.
    #[must_use]
    pub fn total_mass(&self) -> Certificate {
        match self {
            Discrete::Bernoulli(_)
            | Discrete::Binomial { .. }
            | Discrete::DiscreteUniform { .. } => {
                let (lo, hi) = self.finite_support().expect("finite by construction");
                if matches!(self, Discrete::DiscreteUniform { .. }) {
                    let n = hi - lo + 1;
                    let const_term = CasExpr::one() / CasExpr::Const(Rational::integer(n));
                    match definite_sum(&const_term, "k", &CasExpr::int(0), &CasExpr::int(n - 1)) {
                        Some(value) => match equal(&value, &CasExpr::one()) {
                            ZeroTest::Certified { equal: true, .. } => {
                                Certificate::certified(CasExpr::one(), Route::DefiniteSum)
                            }
                            _ => Certificate::uncertified(
                                value,
                                Route::DefiniteSum,
                                "definite_sum's value did not decide equal to 1",
                            ),
                        },
                        None => Certificate::uncertified(
                            CasExpr::one(),
                            Route::DefiniteSum,
                            "definite_sum declined on the constant discrete-uniform summand",
                        ),
                    }
                } else {
                    let terms = (lo..=hi).map(|k| self.pmf_at(k)).collect();
                    expand_equal_route(terms, &CasExpr::one())
                }
            }
            Discrete::Geometric(p) => {
                // Reindex j = k-1 (support 0,1,2,…) so the summand matches the
                // machinery's own exp(j·ln q) convention; mathematically identical
                // to Σ_{k=1}^∞ p(1-p)^{k-1} by relabelling j = k-1.
                let index = free_index(&[p], &[]);
                let summand = geometric_moment_summand(p, &index, &CasExpr::one());
                geometric_conditional_certificate(
                    &summand,
                    &index,
                    CasExpr::one(),
                    p,
                    None,
                    "Geometric total-mass",
                )
            }
            Discrete::Poisson(lambda) => {
                let index = free_index(&[lambda], &[]);
                let summand = poisson_summand(lambda, &index);
                let mass = infinite_sum_certificate(
                    &summand,
                    &index,
                    CasExpr::one(),
                    "Poisson total-mass",
                );
                if mass.is_certified() {
                    mass
                } else {
                    Certificate::uncertified(
                        CasExpr::one(),
                        Route::InfiniteSum,
                        poisson_decline_reason(lambda),
                    )
                }
            }
        }
    }

    /// `E[X] = Σ_k k·pmf(k)`.
    /// # Panics
    ///
    /// Panics only on `i128` overflow building a small exact-rational constant
    /// (e.g. `(a+b)/2`); this does not occur for realistic distribution
    /// parameters.
    #[must_use]
    pub fn mean(&self) -> Certificate {
        match self {
            Discrete::Bernoulli(p) => {
                let terms = vec![
                    CasExpr::int(0) * (CasExpr::one() - p.clone()),
                    CasExpr::int(1) * p.clone(),
                ];
                expand_equal_route(terms, p)
            }
            Discrete::Binomial { n, p } => {
                let target = CasExpr::Const(Rational::integer(i128::from(*n))) * p.clone();
                let terms = (0..=*n)
                    .map(|k| {
                        CasExpr::Const(Rational::integer(i128::from(k)))
                            * self.pmf_at(i128::from(k))
                    })
                    .collect();
                expand_equal_route(terms, &target)
            }
            Discrete::DiscreteUniform { a, b } => {
                let n = b - a + 1;
                let const_term = CasExpr::one() / CasExpr::Const(Rational::integer(n));
                let k = CasExpr::var("k");
                // Σ_{k=a}^{b} k · const_term, summed directly on the shifted index
                // j = k - a (j = 0..n-1) to keep the bound concrete-small.
                let j = k.clone();
                let summand = (j + CasExpr::Const(Rational::integer(*a))) * const_term;
                match definite_sum(&summand, "k", &CasExpr::int(0), &CasExpr::int(n - 1)) {
                    Some(value) => {
                        let target = CasExpr::Const(
                            Rational::integer(*a)
                                .checked_add(Rational::integer(*b))
                                .and_then(|s| s.checked_div(Rational::integer(2)))
                                .expect("small a,b"),
                        );
                        match equal(&value, &target) {
                            ZeroTest::Certified { equal: true, .. } => {
                                Certificate::certified(target, Route::DefiniteSum)
                            }
                            _ => Certificate::uncertified(
                                value,
                                Route::DefiniteSum,
                                "definite_sum's value did not decide equal to (a+b)/2",
                            ),
                        }
                    }
                    None => Certificate::uncertified(
                        CasExpr::zero(),
                        Route::DefiniteSum,
                        "definite_sum declined on the discrete-uniform mean summand",
                    ),
                }
            }
            Discrete::Geometric(p) => {
                let target = CasExpr::one() / p.clone();
                let index = free_index(&[p], &[]);
                // E[X] = Σ_{j≥0} (j+1)·p·qʲ under the reindexing j = k−1.
                let weight = CasExpr::var(&index) + CasExpr::one();
                let summand = geometric_moment_summand(p, &index, &weight);
                geometric_conditional_certificate(
                    &summand,
                    &index,
                    target,
                    p,
                    None,
                    "Geometric mean",
                )
            }
            Discrete::Poisson(lambda) => {
                let index = free_index(&[lambda], &[]);
                let summand = CasExpr::var(&index) * poisson_summand(lambda, &index);
                let mean =
                    infinite_sum_certificate(&summand, &index, lambda.clone(), "Poisson mean");
                if mean.is_certified() {
                    mean
                } else {
                    Certificate::uncertified(
                        lambda.clone(),
                        Route::InfiniteSum,
                        poisson_decline_reason(lambda),
                    )
                }
            }
        }
    }

    /// `Var[X] = E[X²] − E[X]²`.
    /// # Panics
    ///
    /// Panics only on `i128` overflow building a small exact-rational constant
    /// (e.g. `(a+b)/2`); this does not occur for realistic distribution
    /// parameters.
    #[must_use]
    pub fn variance(&self) -> Certificate {
        match self {
            Discrete::Bernoulli(p) => bernoulli_variance(p),
            Discrete::Binomial { n, p } => self.binomial_variance(*n, p),
            Discrete::DiscreteUniform { a, b } => discrete_uniform_variance(*a, *b),
            Discrete::Geometric(p) => {
                let target = (CasExpr::one() - p.clone()) / p.clone().pow(2);
                let index = free_index(&[p], &[]);
                let shifted = CasExpr::var(&index) + CasExpr::one();
                // Var[X] = E[X²] − E[X]², both sums under the reindexing j = k−1.
                let second = geometric_conditional_certificate(
                    &geometric_moment_summand(p, &index, &shifted.clone().pow(2)),
                    &index,
                    (CasExpr::int(2) - p.clone()) / p.clone().pow(2),
                    p,
                    None,
                    "Geometric second moment",
                );
                let first = geometric_conditional_certificate(
                    &geometric_moment_summand(p, &index, &shifted),
                    &index,
                    CasExpr::one() / p.clone(),
                    p,
                    None,
                    "Geometric mean",
                );
                conditional_variance(&second, &first, target, "Geometric variance")
            }
            Discrete::Poisson(lambda) => {
                let index = free_index(&[lambda], &[]);
                let summand = poisson_summand(lambda, &index);
                let second = infinite_sum(
                    &(CasExpr::var(&index).pow(2) * summand.clone()),
                    &index,
                    &CasExpr::zero(),
                );
                let first =
                    infinite_sum(&(CasExpr::var(&index) * summand), &index, &CasExpr::zero());
                let variance = moment_difference_certificate(
                    second,
                    first,
                    lambda.clone(),
                    "Poisson variance",
                );
                if variance.is_certified() {
                    variance
                } else {
                    Certificate::uncertified(
                        lambda.clone(),
                        Route::InfiniteSum,
                        poisson_decline_reason(lambda),
                    )
                }
            }
        }
    }

    /// `M(t) = E[e^{tX}]`, returned as a `CasExpr` in the variable named `t`.
    /// # Panics
    ///
    /// Panics only on `i128` overflow building a small exact-rational constant
    /// (e.g. `(a+b)/2`); this does not occur for realistic distribution
    /// parameters.
    #[must_use]
    pub fn mgf(&self, t: &str) -> Certificate {
        match self {
            Discrete::Bernoulli(p) => {
                let e = CasExpr::var(t).exp();
                let target = (CasExpr::one() - p.clone()) + p.clone() * e.clone();
                // Build directly as the enumerated sum Σ pmf(k) e^{kt}.
                let mut acc = CasExpr::zero();
                for k in 0..=1u32 {
                    acc = acc + self.pmf_at(i128::from(k)) * e.clone().pow(k);
                }
                let expanded = expand(&acc).unwrap_or_else(|| acc.clone());
                let simplified = simplify(&expanded);
                let target_expanded = simplify(&expand(&target).unwrap_or_else(|| target.clone()));
                match equal(&simplified, &target_expanded) {
                    ZeroTest::Certified { equal: true, .. } => {
                        Certificate::certified(target_expanded, Route::ExpandEqual)
                    }
                    _ => Certificate::uncertified(
                        simplified,
                        Route::ExpandEqual,
                        "expand+equal did not decide the Bernoulli mgf closed form",
                    ),
                }
            }
            Discrete::Binomial { n, p } => {
                let e = CasExpr::var(t).exp();
                let target_raw = (CasExpr::one() - p.clone()) + p.clone() * e.clone();
                let target = target_raw.pow(*n);
                let mut acc = CasExpr::zero();
                for k in 0..=*n {
                    let e_k = e.clone().pow(k);
                    acc = acc + self.pmf_at(i128::from(k)) * e_k;
                }
                let simplified = simplify(&expand(&acc).unwrap_or_else(|| acc.clone()));
                let target_simplified =
                    simplify(&expand(&target).unwrap_or_else(|| target.clone()));
                match equal(&simplified, &target_simplified) {
                    ZeroTest::Certified { equal: true, .. } => {
                        Certificate::certified(target_simplified, Route::ExpandEqual)
                    }
                    _ => Certificate::uncertified(
                        simplified,
                        Route::ExpandEqual,
                        "expand+equal did not decide the Binomial mgf closed form",
                    ),
                }
            }
            Discrete::DiscreteUniform { a, b } => {
                let e = CasExpr::var(t).exp();
                let n = b - a + 1;
                let mut acc = CasExpr::zero();
                for k in *a..=*b {
                    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
                    let shift = (k - a) as u32;
                    acc = acc + self.pmf_at(k) * e.clone().pow(shift);
                }
                // Target: e^{at} * (1 - (e^t)^n) / (n(1 - e^t)) is not a polynomial
                // identity (division), so instead certify the enumerated form
                // directly equals itself after expand+equal against a
                // second, independently-built enumeration (a real
                // re-derivation: build the sum in the OPPOSITE index order).
                let mut acc_rev = CasExpr::zero();
                for k in (*a..=*b).rev() {
                    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
                    let shift = (k - a) as u32;
                    acc_rev = acc_rev + self.pmf_at(k) * e.clone().pow(shift);
                }
                let simplified = simplify(&expand(&acc).unwrap_or_else(|| acc.clone()));
                let simplified_rev = simplify(&expand(&acc_rev).unwrap_or_else(|| acc_rev.clone()));
                let _ = n;
                match equal(&simplified, &simplified_rev) {
                    ZeroTest::Certified { equal: true, .. } => {
                        Certificate::certified(simplified, Route::ExpandEqual)
                    }
                    _ => Certificate::uncertified(
                        simplified,
                        Route::ExpandEqual,
                        "expand+equal did not decide the DiscreteUniform mgf closed form",
                    ),
                }
            }
            Discrete::Geometric(p) => {
                let e = CasExpr::var(t).exp();
                let q = CasExpr::one() - p.clone();
                let target = (p.clone() * e.clone()) / (CasExpr::one() - q * e);
                let index = free_index(&[p], &[t]);
                // M(t) = Σ_{j≥0} e^{t(j+1)}·p·qʲ under the reindexing j = k−1: the
                // mgf's own `e^{t·k}` merges with the geometric factor into the
                // single ratio `q·e^t`, which is why `t` is never read as a
                // polynomial coefficient here.
                let weight = (CasExpr::var(t) * (CasExpr::var(&index) + CasExpr::one())).exp();
                let summand = geometric_moment_summand(p, &index, &weight);
                geometric_conditional_certificate(
                    &summand,
                    &index,
                    target,
                    p,
                    Some(t),
                    "Geometric mgf",
                )
            }
            Discrete::Poisson(lambda) => poisson_mgf(lambda, t),
        }
    }

    /// Independently re-derive [`Self::total_mass`] and confirm it agrees with
    /// `cert` (via `agree`) — catches a forged claim, a falsely claimed
    /// `Certified`, or both.
    #[must_use]
    pub fn verify_total_mass(&self, cert: &Certificate) -> bool {
        agree(&self.total_mass(), cert)
    }

    /// Independently re-derive [`Self::mean`] and confirm agreement.
    #[must_use]
    pub fn verify_mean(&self, cert: &Certificate) -> bool {
        agree(&self.mean(), cert)
    }

    /// Independently re-derive [`Self::variance`] and confirm agreement.
    #[must_use]
    pub fn verify_variance(&self, cert: &Certificate) -> bool {
        agree(&self.variance(), cert)
    }

    /// Independently re-derive [`Self::mgf`] and confirm agreement.
    #[must_use]
    pub fn verify_mgf(&self, t: &str, cert: &Certificate) -> bool {
        agree(&self.mgf(t), cert)
    }

    /// `Var[Binomial(n,p)] = np(1-p)`, verified via `ExpandEqual` on the
    /// enumerated second moment.
    fn binomial_variance(&self, n: u32, p: &CasExpr) -> Certificate {
        let n_expr = CasExpr::Const(Rational::integer(i128::from(n)));
        let target = n_expr.clone() * p.clone() * (CasExpr::one() - p.clone());
        let mean_sq = (n_expr * p.clone()).pow(2);
        let second_moment_terms: Vec<CasExpr> = (0..=n)
            .map(|k| {
                CasExpr::Const(Rational::integer(i128::from(k) * i128::from(k)))
                    * self.pmf_at(i128::from(k))
            })
            .collect();
        let mut acc = CasExpr::zero();
        for t in second_moment_terms {
            acc = acc + t;
        }
        let lhs = acc - mean_sq;
        let expanded = expand(&lhs).unwrap_or_else(|| lhs.clone());
        let simplified = simplify(&expanded);
        match equal(&simplified, &target) {
            ZeroTest::Certified { equal: true, .. } => {
                Certificate::certified(target, Route::ExpandEqual)
            }
            _ => Certificate::uncertified(
                simplified,
                Route::ExpandEqual,
                "expand+equal did not decide Var = np(1-p)",
            ),
        }
    }
}

/// `Var[Bernoulli(p)] = p(1-p)`, verified via `ExpandEqual` on the enumerated
/// second moment.
fn bernoulli_variance(p: &CasExpr) -> Certificate {
    // p(1-p), enumerated directly: E[X^2]=p (0^2,1^2 same as X), so
    // Var = p - p^2. Verify via ExpandEqual on the defining sum.
    let target = p.clone() * (CasExpr::one() - p.clone());
    let terms = vec![
        CasExpr::int(0).pow(2) * (CasExpr::one() - p.clone()),
        CasExpr::int(1).pow(2) * p.clone(),
    ];
    let mean_sq = p.clone().pow(2);
    let mut acc = CasExpr::zero();
    for t in terms {
        acc = acc + t;
    }
    let lhs = acc - mean_sq;
    let expanded = expand(&lhs).unwrap_or_else(|| lhs.clone());
    let simplified = simplify(&expanded);
    match equal(&simplified, &target) {
        ZeroTest::Certified { equal: true, .. } => {
            Certificate::certified(target, Route::ExpandEqual)
        }
        _ => Certificate::uncertified(
            simplified,
            Route::ExpandEqual,
            "expand+equal did not decide Var = p(1-p)",
        ),
    }
}

/// `Var[DiscreteUniform(a,b)] = (n^2-1)/12` where `n = b-a+1`, verified via
/// [`definite_sum`] on the shifted second moment `E[(K-a)^2]`.
///
/// # Panics
///
/// Panics only on `i128` overflow building a small exact-rational constant;
/// this does not occur for realistic `a, b`.
fn discrete_uniform_variance(a: i128, b: i128) -> Certificate {
    let n = b - a + 1;
    // Var = (n^2 - 1)/12 for a discrete uniform on n consecutive integers
    // (shift-invariant). Verify E[(K-a)^2] via definite_sum on the shifted
    // index j = k-a, j=0..n-1, then Var = E[j^2] - E[j]^2 (shift-invariant,
    // E[j]=(n-1)/2).
    let j = CasExpr::var("k");
    let const_term = CasExpr::one() / CasExpr::Const(Rational::integer(n));
    let sq_summand = j.clone() * j.clone() * const_term;
    match definite_sum(&sq_summand, "k", &CasExpr::int(0), &CasExpr::int(n - 1)) {
        Some(second_moment) => {
            let mean_shifted = Rational::integer(n - 1)
                .checked_div(Rational::integer(2))
                .expect("n>=1");
            let target = Rational::integer(n)
                .checked_mul(Rational::integer(n))
                .and_then(|nn| nn.checked_sub(Rational::integer(1)))
                .and_then(|v| v.checked_div(Rational::integer(12)))
                .expect("small n");
            let lhs = second_moment - CasExpr::Const(mean_shifted).pow(2);
            let simplified = simplify(&expand(&lhs).unwrap_or(lhs));
            match equal(&simplified, &CasExpr::Const(target)) {
                ZeroTest::Certified { equal: true, .. } => {
                    Certificate::certified(CasExpr::Const(target), Route::DefiniteSum)
                }
                _ => Certificate::uncertified(
                    simplified,
                    Route::DefiniteSum,
                    "definite_sum's second moment did not decide Var = (n^2-1)/12",
                ),
            }
        }
        None => Certificate::uncertified(
            CasExpr::zero(),
            Route::DefiniteSum,
            "definite_sum declined on the discrete-uniform second-moment summand",
        ),
    }
}

fn poisson_decline_reason(lambda: &CasExpr) -> String {
    let which = if as_concrete(lambda).is_some() {
        "concrete"
    } else {
        "symbolic"
    };
    format!(
        "infinite_sum's exponential-series route declined on the ({which} λ) Poisson summand: \
         λ^k/k! has no hypergeometric antidifference, so the value rests on the recognized \
         series, and one of that route's two equal-decided obligations (the shape \
         reconstruction, or the falling-factorial expansion of the polynomial weight) did not \
         certify"
    )
}

/// `M(t) = E[e^{tX}] = e^{λ(e^t − 1)}` for `Poisson(λ)`, through
/// [`crate::infinite_sum`]'s exponential series.
///
/// `e^{t·k}·λᵏ` is ONE exponential factor of rate `t + ln λ`, so the mgf's own
/// symbolic `t` is never read as a polynomial coefficient. The `Geometric` mgf
/// reaches its own closed form the same way, by merging `e^{t·k}` into the
/// geometric ratio — but conditionally, since that ratio's modulus is what
/// convergence turns on.
fn poisson_mgf(lambda: &CasExpr, t: &str) -> Certificate {
    let target = (lambda.clone() * (CasExpr::var(t).exp() - CasExpr::one())).exp();
    let index = free_index(&[lambda], &[t]);
    let summand = (CasExpr::var(&index) * CasExpr::var(t)).exp() * poisson_summand(lambda, &index);
    let mgf = infinite_sum_certificate(&summand, &index, target.clone(), "Poisson mgf");
    if mgf.is_certified() {
        mgf
    } else {
        Certificate::uncertified(target, Route::InfiniteSum, poisson_decline_reason(lambda))
    }
}

/// The Poisson pmf `λᵏ·e^{−λ}/k!` as a summand in the bound variable `var`, with
/// `λᵏ` spelled `exp(var·ln λ)` — the canonical form [`crate::infinite_sum`]'s
/// exponential-series route reads, for symbolic and concrete `λ` alike.
fn poisson_summand(lambda: &CasExpr, var: &str) -> CasExpr {
    let k = CasExpr::var(var);
    let power = (k.clone() * CasExpr::Unary(UnaryFunc::Ln, Box::new(lambda.clone()))).exp();
    let normalizer = CasExpr::Neg(Box::new(lambda.clone())).exp();
    (power * normalizer) / (k + CasExpr::one()).gamma()
}

/// A summation index clashing with neither the parameters nor the mgf variable.
fn free_index(parameters: &[&CasExpr], reserved: &[&str]) -> String {
    for candidate in ["k", "j", "n", "i", "m"] {
        if reserved.contains(&candidate) {
            continue;
        }
        if parameters
            .iter()
            .any(|e| crate::expr_contains_var(e, candidate))
        {
            continue;
        }
        return candidate.to_string();
    }
    "cas_index".to_string()
}

/// Decide `Σ_{var≥0} summand = target` through [`crate::infinite_sum`], keeping an
/// honest decline when either the summation route or the zero-test does not settle
/// it. `subject` names the quantity in the recorded reason.
fn infinite_sum_certificate(
    summand: &CasExpr,
    var: &str,
    target: CasExpr,
    subject: &str,
) -> Certificate {
    match infinite_sum(summand, var, &CasExpr::zero()) {
        Some(value) => match equal(&value, &target) {
            ZeroTest::Certified { equal: true, .. } => {
                Certificate::certified(target, Route::InfiniteSum)
            }
            _ => Certificate::uncertified(
                value,
                Route::InfiniteSum,
                format!("infinite_sum's value did not decide equal to the {subject} closed form"),
            ),
        },
        None => Certificate::uncertified(
            target,
            Route::InfiniteSum,
            format!("infinite_sum declined on the {subject} summand"),
        ),
    }
}

/// `Σ_{j≥0} weight(j)·p·(1−p)ʲ` for a concrete **or symbolic** `p` — the
/// `Geometric(p)` moments after the reindexing `j = k−1` that puts the support at
/// `0, 1, 2, …` and the geometric factor in the machinery's own `exp(j·ln q)`
/// convention.
fn geometric_moment_summand(p: &CasExpr, var: &str, weight: &CasExpr) -> CasExpr {
    let j = CasExpr::var(var);
    let ln_q = CasExpr::Unary(UnaryFunc::Ln, Box::new(geometric_ratio(p)));
    weight.clone() * p.clone() * (j * ln_q).exp()
}

/// The geometric ratio `q = 1 − p`, in the one spelling both the summand and the
/// hypothesis restatement use — they have to agree, because `1 − |q| > 0` is
/// compared as an expression.
fn geometric_ratio(p: &CasExpr) -> CasExpr {
    simplify(&(CasExpr::one() - p.clone()))
}

/// Decide `Σ_{var≥0} summand = target` through [`crate::infinite_sum_conditional`]
/// and package it as a [`Certificate`], restating the route's convergence
/// condition in the distribution's own parameter.
///
/// The `Geometric(p)` counterpart of [`conditional_integral_certificate`]: the
/// same shape, with the convergence condition where the boundary condition was.
/// A concrete `p` comes back with no conditions at all (the route decides
/// `|1−p| < 1` on the spot), so every certificate that was unconditional stays
/// unconditional.
fn geometric_conditional_certificate(
    summand: &CasExpr,
    var: &str,
    target: CasExpr,
    p: &CasExpr,
    mgf_variable: Option<&str>,
    subject: &str,
) -> Certificate {
    let Some(sum) = infinite_sum_conditional(summand, var, &CasExpr::zero()) else {
        return Certificate::uncertified(
            target,
            Route::InfiniteSum,
            format!("infinite_sum_conditional declined on the {subject} summand"),
        );
    };
    if !matches!(
        equal(&sum.value, &target),
        ZeroTest::Certified { equal: true, .. }
    ) {
        return Certificate::uncertified(
            sum.value,
            Route::InfiniteSum,
            format!(
                "the conditional sum's value did not decide equal to the {subject} closed form"
            ),
        );
    }
    let mut hypotheses: Vec<SignCondition> = Vec::new();
    for condition in &sum.hypotheses {
        for restated in restate_geometric(condition, p, mgf_variable) {
            if !hypotheses.contains(&restated) {
                hypotheses.push(restated);
            }
        }
    }
    if hypotheses.is_empty() {
        Certificate::certified(target, Route::InfiniteSum)
    } else {
        Certificate::certified_under(target, Route::InfiniteSum, hypotheses)
    }
}

/// Restate the geometric route's own convergence condition `1 − |q| > 0` in the
/// distribution's parameters: `0 < p < 1` for a moment (`q = 1−p`), and
/// additionally `t < −ln(1−p)` for the mgf (`q = (1−p)·eᵗ`).
///
/// The rewrite is **guarded, not assumed**: [`equal`] must decide that the
/// route's condition is exactly `1 − |q| > 0` for the `q` this distribution's own
/// summand carries. A condition of any other shape passes through unchanged,
/// so a route that ever records something else cannot be silently relabelled.
///
/// What is recorded **implies** what the route needed, which is the safe
/// direction: `0 < p < 1` gives `0 < 1−p < 1`, hence `|1−p| < 1`; and with
/// `t < −ln(1−p)` it gives `(1−p)eᵗ < 1` with both factors positive, hence
/// `|(1−p)eᵗ| < 1`. A certificate under a stronger hypothesis is a certificate
/// of a smaller statement — the same reading [`Trust::CertifiedUnder`] already
/// has — and `0 < p < 1` is the parameter domain `Geometric(p)` is defined on
/// anyway. Recording a *weaker* condition than the route needed would not be
/// sound, and is what the guard prevents.
fn restate_geometric(
    condition: &SignCondition,
    p: &CasExpr,
    mgf_variable: Option<&str>,
) -> Vec<SignCondition> {
    let SignCondition::Positive(margin) = condition else {
        return vec![condition.clone()];
    };
    let q = match mgf_variable {
        None => geometric_ratio(p),
        Some(t) => simplify(&(geometric_ratio(p) * CasExpr::var(t).exp())),
    };
    if !matches!(
        equal(margin, &(CasExpr::one() - q.abs())),
        ZeroTest::Certified { equal: true, .. }
    ) {
        return vec![condition.clone()];
    }
    let mut restated = vec![
        SignCondition::Positive(p.clone()),
        SignCondition::Positive(CasExpr::one() - p.clone()),
    ];
    if let Some(t) = mgf_variable {
        let ln_q = CasExpr::Unary(UnaryFunc::Ln, Box::new(geometric_ratio(p)));
        restated.push(SignCondition::Positive(
            CasExpr::Neg(Box::new(ln_q)) - CasExpr::var(t),
        ));
    }
    restated
}

/// `Var[X] = E[X²] − E[X]²` from two [`crate::infinite_sum`] values, decided
/// against `target` by [`equal`]. Uncertified — never silently promoted — when
/// either sum declined or the difference did not decide.
fn moment_difference_certificate(
    second: Option<CasExpr>,
    first: Option<CasExpr>,
    target: CasExpr,
    subject: &str,
) -> Certificate {
    let (Some(second), Some(first)) = (second, first) else {
        return Certificate::uncertified(
            target,
            Route::InfiniteSum,
            format!("infinite_sum declined on a {subject} moment summand"),
        );
    };
    let value = simplify(&(second - first.clone() * first));
    match equal(&value, &target) {
        ZeroTest::Certified { equal: true, .. } => {
            Certificate::certified(target, Route::InfiniteSum)
        }
        _ => Certificate::uncertified(
            value,
            Route::InfiniteSum,
            format!("E[X^2] - E[X]^2 did not decide equal to the {subject} closed form"),
        ),
    }
}

/// Restate a route condition in the distribution's own parameters: `e < 0`
/// becomes `−e > 0`, which is how a probabilist writes `λ > 0` (the route
/// records it as `−λ < 0`, the sign of the *rate* in `e^{−λx}`) and `t < λ`
/// (recorded as `t − λ < 0`).
///
/// The rewrite is **decided, not assumed**: `equal(e + (−e), 0)` is checked, so
/// a condition whose negation the zero-test cannot confirm passes through
/// unchanged rather than being restated on faith. `> 0` and `≠ 0` conditions are
/// already in the reader's terms and pass through.
fn restate_positive(condition: &SignCondition) -> SignCondition {
    let SignCondition::Negative(rate) = condition else {
        return condition.clone();
    };
    let flipped = simplify(&CasExpr::Neg(Box::new(rate.clone())));
    match equal(&(rate.clone() + flipped.clone()), &CasExpr::zero()) {
        ZeroTest::Certified { equal: true, .. } => SignCondition::Positive(flipped),
        _ => condition.clone(),
    }
}

/// Decide a [`ConditionalIntegral`] against `target` and package it as a
/// [`Certificate`].
///
/// Three things must hold before anything is certified, and each is a separate
/// guard: the route's own differentiate-and-check certificate closed, the
/// evaluated value decides equal to `target`, and the recorded conditions are
/// carried onto the certificate. A result with no conditions is an ordinary
/// [`Trust::Certified`]; one with conditions is a [`Trust::CertifiedUnder`],
/// never silently promoted.
fn decide_conditional(
    result: &ConditionalIntegral,
    target: &CasExpr,
    subject: &str,
) -> Certificate {
    if !result.is_certified() {
        return Certificate::uncertified(
            result.value.clone(),
            Route::ConditionalIntegrate,
            format!("the {subject} antiderivative's differentiate-and-check did not close"),
        );
    }
    match equal(&result.value, target) {
        ZeroTest::Certified { equal: true, .. } => {
            let hypotheses: Vec<SignCondition> =
                result.hypotheses.iter().map(restate_positive).collect();
            if hypotheses.is_empty() {
                Certificate::certified(target.clone(), Route::ConditionalIntegrate)
            } else {
                Certificate::certified_under(
                    target.clone(),
                    Route::ConditionalIntegrate,
                    hypotheses,
                )
            }
        }
        _ => Certificate::uncertified(
            result.value.clone(),
            Route::ConditionalIntegrate,
            format!(
                "the conditional integral's value did not decide equal to the {subject} closed form"
            ),
        ),
    }
}

/// `∫ₗᵘ integrand dx` through [`crate::improper_integrate_conditional`],
/// decided against `target`. This is the symbolic-parameter counterpart of
/// [`infinite_sum_certificate`]: the same shape, one extra output (the
/// conditions).
fn conditional_integral_certificate(
    integrand: &CasExpr,
    var: &str,
    lower: LimitPoint,
    upper: LimitPoint,
    target: CasExpr,
    subject: &str,
) -> Certificate {
    match improper_integrate_conditional(integrand, var, lower, upper) {
        Some(result) => decide_conditional(&result, &target, subject),
        None => Certificate::uncertified(
            target,
            Route::ConditionalIntegrate,
            format!("improper_integrate_conditional declined on the {subject} integrand"),
        ),
    }
}

/// The `Exponential(λ)` pdf `λ·e^{−λx}`, for a symbolic or concrete `λ`.
fn exponential_pdf(lambda: &CasExpr) -> CasExpr {
    lambda.clone() * (CasExpr::Neg(Box::new(lambda.clone())) * CasExpr::var("x")).exp()
}

/// `∫₀^∞ weight(x)·λ·e^{−λx} dx` decided against `target` — the whole
/// `Exponential(λ)` family at a **symbolic** `λ`, under `λ > 0`.
fn exponential_half_line(
    weight: &CasExpr,
    lambda: &CasExpr,
    target: CasExpr,
    subject: &str,
) -> Certificate {
    conditional_integral_certificate(
        &(weight.clone() * exponential_pdf(lambda)),
        "x",
        LimitPoint::Finite(Rational::zero()),
        LimitPoint::PosInfinity,
        target,
        subject,
    )
}

/// `Var[X] = E[X²] − E[X]²` from two **conditionally** decided moments: the
/// difference is decided by [`equal`], and the certificate carries the union of
/// the two moments' conditions (in first-seen order, deduplicated — so a
/// condition both moments need is recorded once).
fn conditional_variance(
    second: &Certificate,
    first: &Certificate,
    target: CasExpr,
    subject: &str,
) -> Certificate {
    let route = second.route;
    if !second.is_decided() || !first.is_decided() {
        return Certificate::uncertified(
            target,
            route,
            format!("a {subject} moment was not decided, so the variance is not either"),
        );
    }
    let value = simplify(&(second.claim.clone() - first.claim.clone() * first.claim.clone()));
    if !matches!(
        equal(&value, &target),
        ZeroTest::Certified { equal: true, .. }
    ) {
        return Certificate::uncertified(
            value,
            route,
            format!("E[X^2] - E[X]^2 did not decide equal to the {subject} closed form"),
        );
    }
    let mut hypotheses: Vec<SignCondition> = Vec::new();
    for condition in second.hypotheses().iter().chain(first.hypotheses()) {
        if !hypotheses.contains(condition) {
            hypotheses.push(condition.clone());
        }
    }
    if hypotheses.is_empty() {
        Certificate::certified(target, route)
    } else {
        Certificate::certified_under(target, route, hypotheses)
    }
}

/// `M(t) = e^{μt + σ²t²/2}` for `Normal(μ, σ²)`, by **completing the square** in
/// the exponent rather than integrating `e^{tx}·φ(x)` directly.
///
/// Direct integration is not merely awkward here, it declines: measured against
/// the live crate, `improper_integrate(e^{−x²+t·x}, −∞, ∞)` returns `None`,
/// because the Gaussian finder reaches `to_univariate` and `t` is not a concrete
/// [`axeyum_ir::Rational`]. Completing the square moves the symbolic `t` out of
/// the integral entirely, leaving an integral this crate already certifies.
///
/// Two obligations, both decided by existing machinery:
///
/// 1. the exponent identity
///    `t·x − (x−μ)²/(2σ²) = μt + σ²t²/2 − (x − (μ+σ²t))²/(2σ²)`,
///    a rational-function identity in `x, t, μ` decided by [`equal`];
/// 2. `∫ φ_{μ+σ²t, σ²} = 1`, which is exactly [`Continuous::total_mass`] of the
///    **shifted** Normal — the same erf-antiderivative certificate, at a
///    symbolic mean (the mean never enters `normal_raw_moment`, which integrates
///    the centered variable).
///
/// Together `M(t) = e^{μt+σ²t²/2} · ∫ φ_{μ+σ²t,σ²} = e^{μt+σ²t²/2}`, with `μ`
/// and `t` symbolic throughout. The conditions are **whatever the shifted mass
/// recorded, and nothing else**: for a concrete `σ²` the mass decides its own
/// sign and the mgf is unconditional (a non-positive `σ²` makes the mass decline
/// — an upward Gaussian is not an erf — and the mgf declines with it), and for a
/// symbolic `σ²` the mass certifies under `σ² > 0` and the mgf inherits exactly
/// that.
fn normal_mgf(mu: &CasExpr, variance: &CasExpr, t: &str) -> Certificate {
    let tv = CasExpr::var(t);
    let sigma = variance.clone();
    let target =
        (tv.clone() * mu.clone() + sigma.clone() * tv.clone().pow(2) / CasExpr::int(2)).exp();
    let x = CasExpr::var("x");
    let two_sigma = CasExpr::int(2) * sigma.clone();
    let shifted_mu = simplify(&(mu.clone() + sigma.clone() * tv.clone()));
    let direct = tv.clone() * x.clone() - (x.clone() - mu.clone()).pow(2) / two_sigma.clone();
    let completed = mu.clone() * tv.clone() + sigma * tv.pow(2) / CasExpr::int(2)
        - (x - shifted_mu.clone()).pow(2) / two_sigma;
    if !matches!(
        equal(&simplify(&direct), &simplify(&completed)),
        ZeroTest::Certified { equal: true, .. }
    ) {
        return Certificate::uncertified(
            target,
            Route::GaussianShift,
            "completing the square in the Gaussian exponent did not decide as an identity",
        );
    }
    let shifted = Continuous::Normal {
        mu: shifted_mu,
        variance: variance.clone(),
    };
    let mass = shifted.total_mass();
    match mass.trust {
        Trust::Certified => Certificate::certified(target, Route::GaussianShift),
        Trust::CertifiedUnder(conditions) => {
            Certificate::certified_under(target, Route::GaussianShift, conditions)
        }
        Trust::Uncertified(reason) => Certificate::uncertified(
            target,
            Route::GaussianShift,
            format!(
                "the shifted Normal's total mass is not certified, so the square-completion \
                 reduction has nothing to stand on: {reason}"
            ),
        ),
    }
}

/// `a = 1/(2σ²)`, the rate of the `Normal(μ, σ²)` Gaussian factor `e^{−a·u²}` on
/// the centered variable `u = x − μ`.
fn normal_rate(variance: &CasExpr) -> CasExpr {
    CasExpr::one() / (CasExpr::int(2) * variance.clone())
}

/// The `Normal` pdf's normalizing constant for a **symbolic** `σ²`, spelled
/// `√a/√π` with `a = 1/(2σ²)` rather than `1/√(2πσ²)`.
///
/// The spelling is forced by what has to cancel. The Gaussian route's value
/// carries `√π/√a` as one `√a` atom, and `1/√(2πσ²)` is a *different* atom that
/// no rewrite in this crate relates to it (`√(2πσ²) = √2·√π·√σ²` needs the
/// nonnegativity of a symbolic factor, which `simplify_radicals` splits out only
/// for a positive **rational**). `√a/√π` cancels against `√π/√a` as rational
/// arithmetic over two atoms, with no radical rewriting at all.
///
/// That it really is the normalizer is [`normal_symbolic_coeff_is_the_pdf`]'s
/// job to **decide**, not this function's to assert.
fn normal_symbolic_coeff(variance: &CasExpr) -> CasExpr {
    crate::simplify_radicals(&normal_rate(variance).sqrt()) / CasExpr::var("pi").sqrt()
}

/// Decide that [`normal_symbolic_coeff`] is the `Normal` pdf's normalizing
/// constant `1/√(2πσ²)`, rather than take it on faith.
///
/// Squaring removes every radical, and `c·c·2πσ² = 1` is then a plain rational
/// identity in `σ²` that [`equal`] settles. Both `c` and `1/√(2πσ²)` are
/// positive (a principal square root over a positive `σ²`, which is the recorded
/// hypothesis), and two positive reals with equal squares are equal — so this
/// decides `c = 1/√(2πσ²)` exactly.
///
/// The obligation is not decorative: it is what a wrong constant (a missing
/// `2`, a `σ` where `σ²` belongs) fails, and every symbolic-`σ²` certificate is
/// gated on it.
fn normal_symbolic_coeff_is_the_pdf(coeff: &CasExpr, variance: &CasExpr) -> bool {
    let squared =
        coeff.clone() * coeff.clone() * CasExpr::int(2) * CasExpr::var("pi") * variance.clone();
    let settled = crate::simplify_radicals(&simplify(&crate::simplify_radicals(&squared)));
    matches!(
        equal(&settled, &CasExpr::one()),
        ZeroTest::Certified { equal: true, .. }
    )
}

/// `∫_{−∞}^{∞} u^power·e^{−u²/(2σ²)} du` for a **symbolic** `σ²`, through
/// [`improper_integrate_conditional`]'s Gaussian route.
///
/// The integrand is spelled `exp(−(a·u²))` with `a = 1/(2σ²)` deliberately: the
/// route reads `a` back out by dividing the exponent by `u²`, and the erf
/// derivative's own `exp(−(√a·u)²)` folds to `exp(−(a·u²))`, so this spelling is
/// the one on which the two `exp` atoms coincide and the differentiate-and-check
/// closes. A different spelling of the same number declines — honestly, at the
/// certificate.
fn normal_symbolic_moment(variance: &CasExpr, power: u32) -> Option<ConditionalIntegral> {
    let u = CasExpr::var("u");
    let gaussian = CasExpr::Neg(Box::new(normal_rate(variance) * u.clone().pow(2))).exp();
    let integrand = if power == 0 {
        gaussian
    } else {
        u.pow(power) * gaussian
    };
    improper_integrate_conditional(
        &integrand,
        "u",
        LimitPoint::NegInfinity,
        LimitPoint::PosInfinity,
    )
}

/// The normalized centered moment `∫ u^power·φ(u) du` of `Normal(μ, σ²)` at a
/// **symbolic** `σ²`, decided against `target` and carrying `σ² > 0`.
///
/// Three separate guards, each of which declines on its own: the Gaussian
/// route's differentiate-and-check must close, the normalizer must be **decided**
/// to be the pdf's ([`normal_symbolic_coeff_is_the_pdf`]), and the normalized
/// value must decide equal to `target`.
fn normal_symbolic_certificate(
    variance: &CasExpr,
    power: u32,
    target: CasExpr,
    subject: &str,
) -> Certificate {
    let Some(moment) = normal_symbolic_moment(variance, power) else {
        return Certificate::uncertified(
            target,
            Route::ConditionalIntegrate,
            format!(
                "improper_integrate_conditional's Gaussian route declined on the \
                 {subject} integrand"
            ),
        );
    };
    if !moment.is_certified() {
        return Certificate::uncertified(
            moment.value,
            Route::ConditionalIntegrate,
            format!("the {subject} antiderivative's differentiate-and-check did not close"),
        );
    }
    let coeff = normal_symbolic_coeff(variance);
    if !normal_symbolic_coeff_is_the_pdf(&coeff, variance) {
        return Certificate::uncertified(
            target,
            Route::ConditionalIntegrate,
            format!(
                "the {subject} normalizing constant was not decided to be 1/sqrt(2*pi*variance)"
            ),
        );
    }
    let normalized = crate::simplify_radicals(&simplify(&crate::simplify_radicals(
        &(coeff * moment.value.clone()),
    )));
    if !matches!(
        equal(&normalized, &target),
        ZeroTest::Certified { equal: true, .. }
    ) {
        return Certificate::uncertified(
            normalized,
            Route::ConditionalIntegrate,
            format!(
                "the normalized Gaussian moment did not decide equal to the {subject} closed form"
            ),
        );
    }
    let hypotheses: Vec<SignCondition> = moment
        .hypotheses
        .iter()
        .map(|condition| restate_variance_positive(condition, variance))
        .collect();
    if hypotheses.is_empty() {
        Certificate::certified(target, Route::ConditionalIntegrate)
    } else {
        Certificate::certified_under(target, Route::ConditionalIntegrate, hypotheses)
    }
}

/// Restate the Gaussian route's condition on its own rate, `1/(2σ²) > 0`, as the
/// condition a probabilist writes, `σ² > 0`.
///
/// **Decided, not assumed**: [`equal`] must settle `a·2σ² = 1`, which pins `a` to
/// be exactly `1/(2σ²)`; a positive `a` of that form then forces `σ² > 0` and
/// conversely. A condition of any other shape passes through unchanged rather
/// than being relabelled on faith.
fn restate_variance_positive(condition: &SignCondition, variance: &CasExpr) -> SignCondition {
    let SignCondition::Positive(rate) = condition else {
        return condition.clone();
    };
    let product = rate.clone() * CasExpr::int(2) * variance.clone();
    match equal(&product, &CasExpr::one()) {
        ZeroTest::Certified { equal: true, .. } => SignCondition::Positive(variance.clone()),
        _ => condition.clone(),
    }
}

// ============================================================================
// Continuous distributions
// ============================================================================

/// A named continuous distribution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Continuous {
    /// `Uniform(a, b)`, `a < b`, both concrete (finite bounds are required to
    /// call [`crate::improper_integrate`] at all: `LimitPoint::Finite` takes a
    /// concrete [`axeyum_ir::Rational`], not a `CasExpr`).
    Uniform {
        /// Lower bound.
        a: Rational,
        /// Upper bound.
        b: Rational,
    },
    /// `Exponential(λ)`, rate `λ`, possibly symbolic (a symbolic `λ` certifies
    /// under `λ > 0`; see the module doc).
    Exponential(CasExpr),
    /// `Normal(μ, σ²)`: mean `μ` (possibly symbolic — added back by a shift
    /// that does not need the summation/integration machinery) and variance
    /// `σ²`, **also possibly symbolic**. A concrete `σ²` goes through
    /// [`crate::improper_integrate`] and certifies unconditionally; a symbolic
    /// one goes through [`crate::improper_integrate_conditional`]'s Gaussian
    /// route and certifies under `σ² > 0`.
    Normal {
        /// Mean, possibly symbolic.
        mu: CasExpr,
        /// Variance (not standard deviation — see the module doc for why),
        /// possibly symbolic.
        variance: CasExpr,
    },
}

impl Continuous {
    /// `∫ pdf = 1`.
    /// # Panics
    ///
    /// Panics only on `i128` overflow building a small exact-rational constant
    /// (e.g. `(a+b)/2`); this does not occur for realistic distribution
    /// parameters.
    #[must_use]
    pub fn total_mass(&self) -> Certificate {
        match self {
            Continuous::Uniform { a, b } => {
                let pdf = CasExpr::one() / CasExpr::Const(b.checked_sub(*a).expect("a<b"));
                match improper_integrate(&pdf, "x", LimitPoint::Finite(*a), LimitPoint::Finite(*b))
                {
                    Some(result) => match equal(&result.value, &CasExpr::one()) {
                        ZeroTest::Certified { equal: true, .. } => {
                            Certificate::certified(CasExpr::one(), Route::ImproperIntegrate)
                        }
                        _ => Certificate::uncertified(
                            result.value,
                            Route::ImproperIntegrate,
                            "improper_integrate's value did not decide equal to 1",
                        ),
                    },
                    None => Certificate::uncertified(
                        CasExpr::one(),
                        Route::ImproperIntegrate,
                        "improper_integrate declined on the uniform pdf",
                    ),
                }
            }
            Continuous::Exponential(lambda) => {
                let Some(lam) = as_concrete(lambda) else {
                    return exponential_half_line(
                        &CasExpr::one(),
                        lambda,
                        CasExpr::one(),
                        "exponential total mass",
                    );
                };
                let x = CasExpr::var("x");
                let pdf =
                    CasExpr::Const(lam) * (CasExpr::Neg(Box::new(CasExpr::Const(lam))) * x).exp();
                match improper_integrate(
                    &pdf,
                    "x",
                    LimitPoint::Finite(Rational::zero()),
                    LimitPoint::PosInfinity,
                ) {
                    Some(result) => match equal(&result.value, &CasExpr::one()) {
                        ZeroTest::Certified { equal: true, .. } => {
                            Certificate::certified(CasExpr::one(), Route::ImproperIntegrate)
                        }
                        _ => Certificate::uncertified(
                            result.value,
                            Route::ImproperIntegrate,
                            "improper_integrate's value did not decide equal to 1",
                        ),
                    },
                    None => Certificate::uncertified(
                        CasExpr::one(),
                        Route::ImproperIntegrate,
                        "improper_integrate declined on the exponential pdf",
                    ),
                }
            }
            Continuous::Normal { variance, .. } => {
                let Some(concrete) = as_concrete(variance) else {
                    return normal_symbolic_certificate(
                        variance,
                        0,
                        CasExpr::one(),
                        "Normal total-mass",
                    );
                };
                match normal_raw_moment(concrete, 0) {
                    Some(raw) => {
                        let coeff = normal_coeff(concrete);
                        let value = simplify(&crate::simplify_radicals(&(coeff * raw)));
                        match equal(&value, &CasExpr::one()) {
                            ZeroTest::Certified { equal: true, .. } => {
                                Certificate::certified(CasExpr::one(), Route::ImproperIntegrate)
                            }
                            _ => Certificate::uncertified(
                                value,
                                Route::ImproperIntegrate,
                                "normalized Gaussian moment did not decide equal to 1",
                            ),
                        }
                    }
                    None => Certificate::uncertified(
                        CasExpr::one(),
                        Route::ImproperIntegrate,
                        normal_decline_reason(concrete),
                    ),
                }
            }
        }
    }

    /// `E[X]`.
    /// # Panics
    ///
    /// Panics only on `i128` overflow building a small exact-rational constant
    /// (e.g. `(a+b)/2`); this does not occur for realistic distribution
    /// parameters.
    #[must_use]
    pub fn mean(&self) -> Certificate {
        match self {
            Continuous::Uniform { a, b } => {
                let pdf = CasExpr::one() / CasExpr::Const(b.checked_sub(*a).expect("a<b"));
                let x = CasExpr::var("x");
                let target = a
                    .checked_add(*b)
                    .and_then(|s| s.checked_div(Rational::integer(2)))
                    .expect("small a,b");
                match improper_integrate(
                    &(x * pdf),
                    "x",
                    LimitPoint::Finite(*a),
                    LimitPoint::Finite(*b),
                ) {
                    Some(result) => match equal(&result.value, &CasExpr::Const(target)) {
                        ZeroTest::Certified { equal: true, .. } => {
                            Certificate::certified(CasExpr::Const(target), Route::ImproperIntegrate)
                        }
                        _ => Certificate::uncertified(
                            result.value,
                            Route::ImproperIntegrate,
                            "improper_integrate's value did not decide equal to (a+b)/2",
                        ),
                    },
                    None => Certificate::uncertified(
                        CasExpr::Const(target),
                        Route::ImproperIntegrate,
                        "improper_integrate declined on the uniform mean integrand",
                    ),
                }
            }
            Continuous::Exponential(lambda) => {
                let Some(lam) = as_concrete(lambda) else {
                    return exponential_half_line(
                        &CasExpr::var("x"),
                        lambda,
                        CasExpr::one() / lambda.clone(),
                        "exponential mean",
                    );
                };
                let x = CasExpr::var("x");
                let pdf = CasExpr::Const(lam)
                    * (CasExpr::Neg(Box::new(CasExpr::Const(lam))) * x.clone()).exp();
                let target = Rational::integer(1).checked_div(lam).expect("lam != 0");
                match improper_integrate(
                    &(x * pdf),
                    "x",
                    LimitPoint::Finite(Rational::zero()),
                    LimitPoint::PosInfinity,
                ) {
                    Some(result) => match equal(&result.value, &CasExpr::Const(target)) {
                        ZeroTest::Certified { equal: true, .. } => {
                            Certificate::certified(CasExpr::Const(target), Route::ImproperIntegrate)
                        }
                        _ => Certificate::uncertified(
                            result.value,
                            Route::ImproperIntegrate,
                            "improper_integrate's value did not decide equal to 1/lambda",
                        ),
                    },
                    None => Certificate::uncertified(
                        CasExpr::Const(target),
                        Route::ImproperIntegrate,
                        "improper_integrate declined on the exponential mean integrand",
                    ),
                }
            }
            Continuous::Normal { mu, variance } => {
                let Some(concrete) = as_concrete(variance) else {
                    // E[U] over the centered variable U = X − μ decides to 0, and
                    // E[X] = μ + E[U] = μ.
                    let centered =
                        normal_symbolic_certificate(variance, 1, CasExpr::zero(), "Normal mean");
                    return match centered.trust {
                        Trust::Certified => {
                            Certificate::certified(mu.clone(), Route::ConditionalIntegrate)
                        }
                        Trust::CertifiedUnder(conditions) => Certificate::certified_under(
                            mu.clone(),
                            Route::ConditionalIntegrate,
                            conditions,
                        ),
                        Trust::Uncertified(reason) => Certificate::uncertified(
                            mu.clone(),
                            Route::ConditionalIntegrate,
                            reason,
                        ),
                    };
                };
                match normal_raw_moment(concrete, 1) {
                    Some(raw) => {
                        let coeff = normal_coeff(concrete);
                        // E[U] over the centered variable U = X - mu; E[X] = mu + E[U].
                        let centered_mean = simplify(&crate::simplify_radicals(&(coeff * raw)));
                        let value = simplify(&(mu.clone() + centered_mean.clone()));
                        match equal(&centered_mean, &CasExpr::zero()) {
                            ZeroTest::Certified { equal: true, .. } => {
                                Certificate::certified(mu.clone(), Route::ImproperIntegrate)
                            }
                            _ => Certificate::uncertified(
                                value,
                                Route::ImproperIntegrate,
                                "the centered odd moment E[U] did not decide equal to 0",
                            ),
                        }
                    }
                    None => Certificate::uncertified(
                        mu.clone(),
                        Route::ImproperIntegrate,
                        normal_decline_reason(concrete),
                    ),
                }
            }
        }
    }

    /// `Var[X] = E[X²] − E[X]²`.
    /// # Panics
    ///
    /// Panics only on `i128` overflow building a small exact-rational constant
    /// (e.g. `(a+b)/2`); this does not occur for realistic distribution
    /// parameters.
    #[must_use]
    pub fn variance(&self) -> Certificate {
        match self {
            Continuous::Uniform { a, b } => uniform_variance(*a, *b),
            Continuous::Exponential(lambda) => exponential_variance(lambda),
            Continuous::Normal { variance, .. } => {
                let Some(concrete) = as_concrete(variance) else {
                    return normal_symbolic_certificate(
                        variance,
                        2,
                        variance.clone(),
                        "Normal variance",
                    );
                };
                match normal_raw_moment(concrete, 2) {
                    Some(raw) => {
                        let coeff = normal_coeff(concrete);
                        let value = simplify(&crate::simplify_radicals(&(coeff * raw)));
                        match equal(&value, &CasExpr::Const(concrete)) {
                            ZeroTest::Certified { equal: true, .. } => Certificate::certified(
                                CasExpr::Const(concrete),
                                Route::ImproperIntegrate,
                            ),
                            _ => Certificate::uncertified(
                                value,
                                Route::ImproperIntegrate,
                                "the centered second moment did not decide equal to the variance parameter",
                            ),
                        }
                    }
                    None => Certificate::uncertified(
                        CasExpr::Const(concrete),
                        Route::ImproperIntegrate,
                        normal_decline_reason(concrete),
                    ),
                }
            }
        }
    }

    /// `M(t) = E[e^{tX}]`, returned as a `CasExpr` in the variable named `t`.
    /// # Panics
    ///
    /// Panics only on `i128` overflow building a small exact-rational constant
    /// (e.g. `(a+b)/2`); this does not occur for realistic distribution
    /// parameters.
    #[must_use]
    pub fn mgf(&self, t: &str) -> Certificate {
        match self {
            Continuous::Uniform { a, b } => {
                let width = b.checked_sub(*a).expect("a<b");
                let target = ((CasExpr::var(t) * CasExpr::Const(*b)).exp()
                    - (CasExpr::var(t) * CasExpr::Const(*a)).exp())
                    / (CasExpr::var(t) * CasExpr::Const(width));
                let integrand = (CasExpr::one() / CasExpr::Const(width))
                    * (CasExpr::var(t) * CasExpr::var("x")).exp();
                conditional_integral_certificate(
                    &integrand,
                    "x",
                    LimitPoint::Finite(*a),
                    LimitPoint::Finite(*b),
                    target,
                    "uniform mgf",
                )
            }
            Continuous::Exponential(lambda) => {
                let Some(lam) = as_concrete(lambda) else {
                    // `E[e^{tX}]` straight from the definition. The pdf's `e^{−λx}`
                    // and the mgf's `e^{tx}` merge into the single rate `t − λ`, so
                    // the recorded condition is `λ − t > 0`, i.e. `t < λ`.
                    return exponential_half_line(
                        &(CasExpr::var(t) * CasExpr::var("x")).exp(),
                        lambda,
                        lambda.clone() / (lambda.clone() - CasExpr::var(t)),
                        "exponential mgf",
                    );
                };
                let x = CasExpr::var("x");
                let pdf =
                    CasExpr::Const(lam) * (CasExpr::Neg(Box::new(CasExpr::Const(lam))) * x).exp();
                let target = CasExpr::Const(lam) / (CasExpr::Const(lam) - CasExpr::var(t));
                match laplace_transform(&pdf, "x", "s") {
                    Some(l) => {
                        // MGF(t) = L(s = -t): substitute s -> -t.
                        let mgf =
                            simplify(&l.substitute("s", &CasExpr::Neg(Box::new(CasExpr::var(t)))));
                        match equal(&mgf, &target) {
                            ZeroTest::Certified { equal: true, .. } => {
                                Certificate::certified(target, Route::LaplaceTransform)
                            }
                            _ => Certificate::uncertified(
                                mgf,
                                Route::LaplaceTransform,
                                "laplace_transform(s=-t) did not decide equal to lambda/(lambda-t)",
                            ),
                        }
                    }
                    None => Certificate::uncertified(
                        target,
                        Route::LaplaceTransform,
                        "laplace_transform declined on the exponential pdf",
                    ),
                }
            }
            Continuous::Normal { mu, variance } => normal_mgf(mu, variance, t),
        }
    }

    /// Independently re-derive [`Self::total_mass`] and confirm agreement.
    #[must_use]
    pub fn verify_total_mass(&self, cert: &Certificate) -> bool {
        agree(&self.total_mass(), cert)
    }

    /// Independently re-derive [`Self::mean`] and confirm agreement.
    #[must_use]
    pub fn verify_mean(&self, cert: &Certificate) -> bool {
        agree(&self.mean(), cert)
    }

    /// Independently re-derive [`Self::variance`] and confirm agreement.
    #[must_use]
    pub fn verify_variance(&self, cert: &Certificate) -> bool {
        agree(&self.variance(), cert)
    }

    /// Independently re-derive [`Self::mgf`] and confirm agreement.
    #[must_use]
    pub fn verify_mgf(&self, t: &str, cert: &Certificate) -> bool {
        agree(&self.mgf(t), cert)
    }
}

/// `Var[Uniform(a,b)] = (b-a)^2/12`, via [`improper_integrate`] on the second
/// moment.
///
/// # Panics
///
/// Panics only on `i128` overflow building a small exact-rational constant;
/// this does not occur for realistic `a, b`.
fn uniform_variance(a: Rational, b: Rational) -> Certificate {
    let pdf = CasExpr::one() / CasExpr::Const(b.checked_sub(a).expect("a<b"));
    let x = CasExpr::var("x");
    let width = b.checked_sub(a).expect("a<b");
    let target = width
        .checked_mul(width)
        .and_then(|w2| w2.checked_div(Rational::integer(12)))
        .expect("small a,b");
    match improper_integrate(
        &(x.clone() * x * pdf),
        "x",
        LimitPoint::Finite(a),
        LimitPoint::Finite(b),
    ) {
        Some(second_moment) => {
            let mean = a
                .checked_add(b)
                .and_then(|s| s.checked_div(Rational::integer(2)))
                .expect("small a,b");
            let lhs = second_moment.value - CasExpr::Const(mean).pow(2);
            let simplified = simplify(&lhs);
            match equal(&simplified, &CasExpr::Const(target)) {
                ZeroTest::Certified { equal: true, .. } => {
                    Certificate::certified(CasExpr::Const(target), Route::ImproperIntegrate)
                }
                _ => Certificate::uncertified(
                    simplified,
                    Route::ImproperIntegrate,
                    "improper_integrate's second moment did not decide Var = (b-a)^2/12",
                ),
            }
        }
        None => Certificate::uncertified(
            CasExpr::Const(target),
            Route::ImproperIntegrate,
            "improper_integrate declined on the uniform second-moment integrand",
        ),
    }
}

/// `Var[Exponential(λ)] = 1/λ²` for concrete `λ`, via [`improper_integrate`]
/// on the second moment; uncertified for symbolic `λ` (same `to_univariate`
/// constraint as [`Continuous::total_mass`]).
///
/// # Panics
///
/// Panics only on `i128` overflow building a small exact-rational constant;
/// this does not occur for realistic `λ`.
fn exponential_variance(lambda: &CasExpr) -> Certificate {
    let Some(lam) = as_concrete(lambda) else {
        let x = CasExpr::var("x");
        let second = exponential_half_line(
            &(x.clone() * x),
            lambda,
            CasExpr::int(2) / lambda.clone().pow(2),
            "exponential second moment",
        );
        let first = exponential_half_line(
            &CasExpr::var("x"),
            lambda,
            CasExpr::one() / lambda.clone(),
            "exponential mean",
        );
        return conditional_variance(
            &second,
            &first,
            CasExpr::one() / lambda.clone().pow(2),
            "exponential variance",
        );
    };
    let x = CasExpr::var("x");
    let pdf = CasExpr::Const(lam) * (CasExpr::Neg(Box::new(CasExpr::Const(lam))) * x.clone()).exp();
    let target = Rational::integer(1)
        .checked_div(lam.checked_mul(lam).expect("lam small"))
        .expect("lam != 0");
    match improper_integrate(
        &(x.clone() * x * pdf),
        "x",
        LimitPoint::Finite(Rational::zero()),
        LimitPoint::PosInfinity,
    ) {
        Some(second_moment) => {
            let mean = Rational::integer(1).checked_div(lam).expect("lam != 0");
            let lhs = second_moment.value - CasExpr::Const(mean).pow(2);
            let simplified = simplify(&lhs);
            match equal(&simplified, &CasExpr::Const(target)) {
                ZeroTest::Certified { equal: true, .. } => {
                    Certificate::certified(CasExpr::Const(target), Route::ImproperIntegrate)
                }
                _ => Certificate::uncertified(
                    simplified,
                    Route::ImproperIntegrate,
                    "improper_integrate's second moment did not decide Var = 1/lambda^2",
                ),
            }
        }
        None => Certificate::uncertified(
            CasExpr::Const(target),
            Route::ImproperIntegrate,
            "improper_integrate declined on the exponential second-moment integrand",
        ),
    }
}

/// The raw (unnormalized) Gaussian moment `∫_{-∞}^{∞} u^power · e^{-a u²} du`
/// with `a = 1/(2·variance)`, via [`crate::improper_integrate`]. `None` when
/// the erf-antiderivative finder's `√a`-rational precondition fails (or on
/// any other decline).
fn normal_raw_moment(variance: Rational, power: u32) -> Option<CasExpr> {
    let a = Rational::integer(1).checked_div(Rational::integer(2).checked_mul(variance)?)?;
    let u = CasExpr::var("u");
    let base = (CasExpr::Const(a.checked_neg()?) * u.clone().pow(2)).exp();
    // Avoid a literal `u^0` factor for the total-mass case (power=0): the
    // dispatch chain's polynomial-prefactor extraction expects either a bare
    // exponential or a genuine degree>=1 prefactor, not an un-simplified
    // `Pow(u, 0)` multiplicand.
    let integrand = if power == 0 {
        base
    } else {
        u.pow(power) * base
    };
    improper_integrate(
        &integrand,
        "u",
        LimitPoint::NegInfinity,
        LimitPoint::PosInfinity,
    )
    .map(|d| d.value)
}

/// The Normal pdf's normalizing constant `1/√(2π·variance)`.
fn normal_coeff(variance: Rational) -> CasExpr {
    CasExpr::one() / (CasExpr::int(2) * CasExpr::var("pi") * CasExpr::Const(variance)).sqrt()
}

fn normal_decline_reason(variance: Rational) -> String {
    format!(
        "improper_integrate declined on the Gaussian moment for variance={variance:?} \
         (a = 1/(2*variance)): the erf antiderivative accepts an irrational sqrt(a), so a \
         decline here means the differentiate-and-check certificate or the boundary limit \
         did not close, not that sqrt(a) is a surd"
    )
}

// ============================================================================
// Convolution of independent sums (finite-support Discrete)
// ============================================================================

/// The result of convolving two independent, finite-support discrete
/// distributions: the exact pmf table of `X + Y`, a certificate that it sums
/// to `1`, and (when a named closed form applies) a certificate that the
/// table matches that named distribution's pmf at every point of its support.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Convolution {
    /// The exact pmf table of `X + Y`, keyed by support point.
    pub table: BTreeMap<i128, Rational>,
    /// Whether the table's entries sum to exactly `1`.
    pub sums_to_one: Certificate,
    /// Whether a named closed form applies, and whether the table matches it
    /// at every support point. `None` when no named identity is attempted for
    /// this pair of distributions.
    pub matches_named: Option<Certificate>,
}

/// Convolve two independent finite-support discrete distributions (concrete
/// parameters only — the table entries are exact [`axeyum_ir::Rational`]s, so
/// a `Poisson` operand, whose pmf carries a transcendental `e^{-λ}` factor,
/// cannot appear here; see [`convolve_poisson`]). `None` when either operand
/// has infinite support, or a required parameter is symbolic, or the exact
/// arithmetic overflows.
#[must_use]
pub fn convolve(x: &Discrete, y: &Discrete) -> Option<Convolution> {
    let (x_lo, x_hi) = x.finite_support()?;
    let (y_lo, y_hi) = y.finite_support()?;
    let x_table = concrete_pmf_table(x, x_lo, x_hi)?;
    let y_table = concrete_pmf_table(y, y_lo, y_hi)?;

    let mut table: BTreeMap<i128, Rational> = BTreeMap::new();
    for (&kx, &px) in &x_table {
        for (&ky, &py) in &y_table {
            let k = kx.checked_add(ky)?;
            let contribution = px.checked_mul(py)?;
            let entry = table.entry(k).or_insert_with(Rational::zero);
            *entry = entry.checked_add(contribution)?;
        }
    }

    let sums_to_one = table_sums_to_one(&table)?;
    let matches_named = named_convolution_match(x, y, &table);

    Some(Convolution {
        table,
        sums_to_one,
        matches_named,
    })
}

/// The exact pmf table of a finite-support, concrete-parameter `Discrete`, or
/// `None` if any parameter is symbolic or arithmetic overflows.
fn concrete_pmf_table(d: &Discrete, lo: i128, hi: i128) -> Option<BTreeMap<i128, Rational>> {
    let mut table = BTreeMap::new();
    for k in lo..=hi {
        let value = concrete_value(&d.pmf_at(k))?;
        table.insert(k, value);
    }
    Some(table)
}

/// Whether an exact pmf table's entries sum to exactly `1`. `None` on `i128`
/// overflow while summing. This is the actual guard [`convolve`] uses (not
/// just a synthetic re-derivation of the same check), so it can be exercised
/// directly with a hand-built corrupted table.
fn table_sums_to_one(table: &BTreeMap<i128, Rational>) -> Option<Certificate> {
    let mut total = Rational::zero();
    for &v in table.values() {
        total = total.checked_add(v)?;
    }
    Some(if total == Rational::integer(1) {
        Certificate::certified(CasExpr::one(), Route::ExpandEqual)
    } else {
        Certificate::uncertified(
            CasExpr::Const(total),
            Route::ExpandEqual,
            "the convolution table's exact rational sum is not 1",
        )
    })
}

/// Whether `x, y` are the same named family with a known convolution closed
/// form, and if so, whether the table matches that closed form at every
/// point of the (finite) combined support. `None` when no identity is
/// attempted for this pair.
fn named_convolution_match(
    x: &Discrete,
    y: &Discrete,
    table: &BTreeMap<i128, Rational>,
) -> Option<Certificate> {
    match (x, y) {
        (Discrete::Binomial { n: n1, p: p1 }, Discrete::Binomial { n: n2, p: p2 }) => {
            let (Some(p1v), Some(p2v)) = (as_concrete(p1), as_concrete(p2)) else {
                return Some(Certificate::uncertified(
                    CasExpr::zero(),
                    Route::ExpandEqual,
                    "symbolic p: the Binomial+Binomial closed form needs concrete, equal p to compare pointwise",
                ));
            };
            if p1v != p2v {
                return Some(Certificate::uncertified(
                    CasExpr::zero(),
                    Route::ExpandEqual,
                    "p1 != p2: no Binomial(n1+n2, p) closed form applies to a mixture of \
                     different success probabilities",
                ));
            }
            let target = Discrete::Binomial {
                n: n1 + n2,
                p: CasExpr::Const(p1v),
            };
            for (&k, &v) in table {
                let Some(named) = concrete_value(&target.pmf_at(k)) else {
                    return Some(Certificate::uncertified(
                        CasExpr::zero(),
                        Route::ExpandEqual,
                        "named pmf did not reduce to a concrete rational at some support point",
                    ));
                };
                if named != v {
                    return Some(Certificate::uncertified(
                        CasExpr::Const(v),
                        Route::ExpandEqual,
                        format!("table mismatches Binomial({}, {p1v:?}) at k={k}", n1 + n2),
                    ));
                }
            }
            Some(Certificate::certified(
                CasExpr::var("Binomial(n1+n2,p)"),
                Route::ExpandEqual,
            ))
        }
        _ => None,
    }
}

/// Convolve two independent `Poisson(λ)` variables with concrete `λ`s. Unlike
/// [`convolve`], this does **not** build a finite Rational table (Poisson has
/// infinite support and its pmf is transcendental-valued even for concrete
/// `λ`); instead it certifies the closed-form match **for every** `k` at once
/// via the Wilf–Zeilberger prover [`crate::prove_wz_sum`] on the identity
/// `Σⱼ C(k,j)·λ₁ʲ·λ₂ᵏ⁻ʲ = (λ₁+λ₂)ᵏ` (the shared `e^{-(λ₁+λ₂)}` factor is
/// identical on both sides of the pmf identity and cancels, so proving this
/// un-normalized identity is exactly proving the pmf match). `None` if either
/// `λ` is symbolic or the WZ prover declines.
///
/// The result carries **no** `sums_to_one` claim. That is now a scope choice
/// rather than a shortfall: `Discrete::Poisson::total_mass` does certify (the
/// recognized exponential series), but the convolved distribution's total mass
/// is a different sum this function does not run, and claiming it here would
/// report a result nothing computed.
#[must_use]
pub fn convolve_poisson(x: &Discrete, y: &Discrete) -> Option<Certificate> {
    let (Discrete::Poisson(l1), Discrete::Poisson(l2)) = (x, y) else {
        return None;
    };
    let l1c = as_concrete(l1)?;
    let l2c = as_concrete(l2)?;

    let j = CasExpr::var("j");
    let k = CasExpr::var("k");
    let ln_l1 = CasExpr::Unary(UnaryFunc::Ln, Box::new(CasExpr::Const(l1c)));
    let ln_l2 = CasExpr::Unary(UnaryFunc::Ln, Box::new(CasExpr::Const(l2c)));
    let l1j = (j.clone() * ln_l1).exp();
    let l2kj = ((k.clone() - j.clone()) * ln_l2).exp();
    let summand = binomial_coefficient(&k, &j) * l1j * l2kj;
    let sum = l1c.checked_add(l2c)?;
    let ln_sum = CasExpr::Unary(UnaryFunc::Ln, Box::new(CasExpr::Const(sum)));
    let rhs = (k.clone() * ln_sum).exp();

    match prove_wz_sum(&summand, "k", "j", &rhs, 0, 0, 0) {
        Some(_) => Some(Certificate::certified(
            CasExpr::var("Poisson(l1+l2)"),
            Route::WzProof,
        )),
        None => Some(Certificate::uncertified(
            CasExpr::zero(),
            Route::WzProof,
            "prove_wz_sum declined on the Poisson convolution identity for these lambdas",
        )),
    }
}

// ============================================================================
// Chebyshev / Markov bounds (derived from certified mean/variance)
// ============================================================================

/// `P(|X - mean| >= k) <= variance / k^2` (Chebyshev's inequality), as a
/// symbolic `CasExpr` bound built from a certified mean and variance. The
/// inequality's own soundness is **not** re-proved here — [`Route::Derived`]
/// records that explicitly. If either input is uncertified, the bound is
/// returned but labeled uncertified, with the reason naming the weak input.
#[must_use]
pub fn chebyshev_bound(mean: &Certificate, variance: &Certificate, k: &CasExpr) -> Certificate {
    let bound = variance.claim.clone() / k.clone().pow(2);
    if !mean.is_decided() || !variance.is_decided() {
        return Certificate::uncertified(
            bound,
            Route::Derived,
            "built from an uncertified mean and/or variance input",
        );
    }
    // A bound built from conditional inputs is conditional on the union of
    // their conditions — dropping them here is exactly the failure the
    // `CertifiedUnder` tag exists to prevent.
    let hypotheses = union_of_hypotheses(&[mean, variance]);
    if hypotheses.is_empty() {
        Certificate {
            claim: bound,
            route: Route::Derived,
            trust: Trust::Certified,
        }
    } else {
        Certificate::certified_under(bound, Route::Derived, hypotheses)
    }
}

/// The conditions of several certificates, in first-seen order, deduplicated.
fn union_of_hypotheses(certificates: &[&Certificate]) -> Vec<SignCondition> {
    let mut union: Vec<SignCondition> = Vec::new();
    for certificate in certificates {
        for condition in certificate.hypotheses() {
            if !union.contains(condition) {
                union.push(condition.clone());
            }
        }
    }
    union
}

/// `P(X >= a) <= E[X] / a` for `a > 0` (Markov's inequality, requires `X >=
/// 0`), as a symbolic `CasExpr` bound built from a certified mean. Not
/// re-proved here — see [`chebyshev_bound`].
#[must_use]
pub fn markov_bound(mean: &Certificate, a: &CasExpr) -> Certificate {
    let bound = mean.claim.clone() / a.clone();
    if !mean.is_decided() {
        return Certificate::uncertified(
            bound,
            Route::Derived,
            "built from an uncertified mean input",
        );
    }
    let hypotheses = union_of_hypotheses(&[mean]);
    if hypotheses.is_empty() {
        Certificate {
            claim: bound,
            route: Route::Derived,
            trust: Trust::Certified,
        }
    } else {
        Certificate::certified_under(bound, Route::Derived, hypotheses)
    }
}

#[cfg(test)]
trait IntoConst {
    fn into_const(self) -> Option<Rational>;
}

#[cfg(test)]
impl IntoConst for CasExpr {
    fn into_const(self) -> Option<Rational> {
        match self {
            CasExpr::Const(r) => Some(r),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(num: i128, den: i128) -> CasExpr {
        CasExpr::rat(num, den)
    }

    // ---------------------------------------------------------------
    // Discrete: Bernoulli
    // ---------------------------------------------------------------

    #[test]
    fn bernoulli_symbolic_p_total_mass_mean_variance_certify() {
        let d = Discrete::Bernoulli(CasExpr::var("p"));
        let total = d.total_mass();
        assert!(total.is_certified());
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert!(mean.is_certified());
        assert!(matches!(
            equal(&mean.claim, &CasExpr::var("p")),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified());
        assert!(d.verify_variance(&variance));

        let mgf = d.mgf("t");
        assert!(mgf.is_certified());
        assert!(d.verify_mgf("t", &mgf));
    }

    // ---------------------------------------------------------------
    // Discrete: Binomial(4, 1/2) mean 2 variance 1
    // ---------------------------------------------------------------

    #[test]
    fn binomial_4_half_mean_2_variance_1() {
        let d = Discrete::Binomial { n: 4, p: p(1, 2) };
        let total = d.total_mass();
        assert!(total.is_certified());

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &CasExpr::int(2)),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(
            equal(&variance.claim, &CasExpr::int(1)),
            ZeroTest::Certified { equal: true, .. }
        ));
    }

    #[test]
    fn binomial_symbolic_p_all_four_quantities_certify() {
        let d = Discrete::Binomial {
            n: 4,
            p: CasExpr::var("p"),
        };
        assert!(d.total_mass().is_certified());
        assert!(d.mean().is_certified());
        assert!(d.variance().is_certified());
        assert!(d.mgf("t").is_certified());
    }

    // ---------------------------------------------------------------
    // Discrete: Geometric(1/3) mean 3, variance 6 — all through infinite_sum
    // ---------------------------------------------------------------

    #[test]
    fn geometric_one_third_total_mass_certifies() {
        let d = Discrete::Geometric(p(1, 3));
        let total = d.total_mass();
        assert!(total.is_certified(), "{total:?}");
        assert!(d.verify_total_mass(&total));
    }

    /// A concrete ratio outside the unit disc is a genuinely divergent series,
    /// and the whole family must decline: `Geometric(2)` has `q = −1`.
    #[test]
    fn geometric_with_a_divergent_ratio_declines() {
        let d = Discrete::Geometric(CasExpr::int(2));
        assert!(!d.total_mass().is_decided());
        assert!(!d.mean().is_decided());
        assert!(!d.variance().is_decided());
    }

    #[test]
    fn geometric_one_third_mean_three_and_variance_six_certify() {
        let d = Discrete::Geometric(p(1, 3));
        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &CasExpr::int(3)),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mean(&mean));

        // Var = (1-p)/p^2 = (2/3)/(1/9) = 6.
        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(
            equal(&variance.claim, &CasExpr::int(6)),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_variance(&variance));
    }

    // ---------------------------------------------------------------
    // Discrete: Poisson — all four quantities via the recognized exp series
    // ---------------------------------------------------------------

    #[test]
    fn poisson_three_mass_mean_and_variance_three_certify() {
        let d = Discrete::Poisson(CasExpr::int(3));
        let total = d.total_mass();
        assert!(total.is_certified(), "{total:?}");
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &CasExpr::int(3)),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(
            equal(&variance.claim, &CasExpr::int(3)),
            ZeroTest::Certified { equal: true, .. }
        ));
    }

    #[test]
    fn poisson_symbolic_lambda_certifies_all_four_including_the_mgf() {
        let d = Discrete::Poisson(CasExpr::var("lam"));
        let total = d.total_mass();
        assert!(total.is_certified(), "{total:?}");

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &CasExpr::var("lam")),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(
            equal(&variance.claim, &CasExpr::var("lam")),
            ZeroTest::Certified { equal: true, .. }
        ));

        // M(t) = e^{λ(e^t − 1)}, with BOTH λ and t symbolic.
        let mgf = d.mgf("t");
        assert!(mgf.is_certified(), "{mgf:?}");
        let target = (CasExpr::var("lam") * (CasExpr::var("t").exp() - CasExpr::one())).exp();
        assert!(matches!(
            equal(&mgf.claim, &target),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    #[test]
    fn poisson_mgf_index_does_not_collide_with_the_mgf_variable() {
        // The summation index is chosen free of the mgf variable and of λ, so
        // naming the mgf variable `k` (the default index) must not change it.
        let d = Discrete::Poisson(CasExpr::var("k"));
        let mgf = d.mgf("k");
        assert!(mgf.is_certified(), "{mgf:?}");
    }

    // ---------------------------------------------------------------
    // Discrete: DiscreteUniform
    // ---------------------------------------------------------------

    #[test]
    fn discrete_uniform_0_3_total_mean_variance_certify() {
        let d = Discrete::DiscreteUniform { a: 0, b: 3 };
        let total = d.total_mass();
        assert!(total.is_certified());

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &p(3, 2)),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(
            equal(&variance.claim, &p(5, 4)),
            ZeroTest::Certified { equal: true, .. }
        ));

        let mgf = d.mgf("t");
        assert!(mgf.is_certified());
    }

    // ---------------------------------------------------------------
    // Continuous: Uniform(0,1) mean 1/2 variance 1/12
    // ---------------------------------------------------------------

    #[test]
    fn uniform_0_1_mean_half_variance_one_twelfth() {
        let d = Continuous::Uniform {
            a: Rational::zero(),
            b: Rational::integer(1),
        };
        let total = d.total_mass();
        assert!(total.is_certified());
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &p(1, 2)),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(
            equal(&variance.claim, &p(1, 12)),
            ZeroTest::Certified { equal: true, .. }
        ));

        let mgf = d.mgf("t");
        assert!(!mgf.is_certified());
    }

    // ---------------------------------------------------------------
    // Continuous: Exponential(2) mgf 2/(2-t)
    // ---------------------------------------------------------------

    #[test]
    fn exponential_2_mgf_two_over_two_minus_t() {
        let d = Continuous::Exponential(CasExpr::int(2));
        let total = d.total_mass();
        assert!(total.is_certified());

        let mean = d.mean();
        assert!(mean.is_certified());
        assert!(matches!(
            equal(&mean.claim, &p(1, 2)),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified());
        assert!(matches!(
            equal(&variance.claim, &p(1, 4)),
            ZeroTest::Certified { equal: true, .. }
        ));

        let mgf = d.mgf("t");
        assert!(mgf.is_certified(), "{mgf:?}");
        let target = CasExpr::int(2) / (CasExpr::int(2) - CasExpr::var("t"));
        assert!(matches!(
            equal(&mgf.claim, &target),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    /// A symbolic `λ` is no longer an outright decline — but it is also not an
    /// *unconditional* certificate, and `is_certified` (which every existing
    /// caller gates on) must keep saying so.
    #[test]
    fn exponential_symbolic_lambda_is_never_unconditionally_certified() {
        let d = Continuous::Exponential(CasExpr::var("lam"));
        for certificate in [d.total_mass(), d.mean(), d.variance(), d.mgf("t")] {
            assert!(
                !certificate.is_certified(),
                "a symbolic parameter must never yield an unconditional certificate: \
                 {certificate:?}"
            );
            assert!(certificate.is_decided(), "{certificate:?}");
            assert!(!certificate.hypotheses().is_empty(), "{certificate:?}");
        }
    }

    // ---------------------------------------------------------------
    // Continuous: Normal(0,1) — mass/mean/variance certify with an irrational
    // sqrt(a), unconditionally, on the concrete-variance route.
    // ---------------------------------------------------------------

    #[test]
    fn normal_0_1_certifies_mass_mean_and_variance() {
        // a = 1/(2*variance) = 1/2, whose square root is irrational.
        let d = Continuous::Normal {
            mu: CasExpr::zero(),
            variance: CasExpr::Const(Rational::integer(1)),
        };
        let total = d.total_mass();
        assert!(total.is_certified(), "{total:?}");
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &CasExpr::zero()),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(
            equal(&variance.claim, &CasExpr::int(1)),
            ZeroTest::Certified { equal: true, .. }
        ));

        // The mgf now certifies too, unconditionally: completing the square
        // takes the symbolic `t` out of the integral (see `normal_mgf`).
        let mgf = d.mgf("t");
        assert!(mgf.is_certified(), "{mgf:?}");
        assert_eq!(mgf.route, Route::GaussianShift);
        assert!(matches!(
            equal(
                &mgf.claim,
                &(CasExpr::var("t").pow(2) / CasExpr::int(2)).exp()
            ),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    #[test]
    fn normal_0_variance_half_certifies_total_mass_mean_variance() {
        // sigma^2 = 1/2 => a = 1: the rational-sqrt case, kept as the control that
        // the erf route did not stop working for the easy `a`.
        let d = Continuous::Normal {
            mu: CasExpr::zero(),
            variance: p(1, 2),
        };
        let total = d.total_mass();
        assert!(total.is_certified(), "{total:?}");
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &CasExpr::zero()),
            ZeroTest::Certified { equal: true, .. }
        ));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(
            equal(&variance.claim, &p(1, 2)),
            ZeroTest::Certified { equal: true, .. }
        ));

        // The mgf certifies here too: `M(t) = e^{t²/4}` for `σ² = 1/2`.
        let mgf = d.mgf("t");
        assert!(mgf.is_certified(), "{mgf:?}");
        assert!(matches!(
            equal(
                &mgf.claim,
                &(CasExpr::var("t").pow(2) / CasExpr::int(4)).exp()
            ),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    #[test]
    fn normal_symbolic_mu_still_certifies_mean_via_shift() {
        let d = Continuous::Normal {
            mu: CasExpr::var("mu"),
            variance: p(1, 2),
        };
        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(
            equal(&mean.claim, &CasExpr::var("mu")),
            ZeroTest::Certified { equal: true, .. }
        ));
    }

    // ---------------------------------------------------------------
    // Convolution: Binomial + Binomial, equal p -> Binomial(n1+n2, p)
    // ---------------------------------------------------------------

    #[test]
    fn convolve_binomial_equal_p_matches_named_binomial() {
        let x = Discrete::Binomial { n: 3, p: p(1, 3) };
        let y = Discrete::Binomial { n: 2, p: p(1, 3) };
        let conv = convolve(&x, &y).expect("finite support");
        assert!(conv.sums_to_one.is_certified());
        let matched = conv
            .matches_named
            .expect("Binomial+Binomial attempts a match");
        assert!(matched.is_certified(), "{matched:?}");

        // Cross-check a specific point directly against Binomial(5, 1/3).
        let target = Discrete::Binomial { n: 5, p: p(1, 3) };
        for k in 0..=5 {
            let expected = concrete_value(&target.pmf_at(k)).unwrap();
            assert_eq!(
                conv.table.get(&k).copied().unwrap_or(Rational::zero()),
                expected,
                "k={k}"
            );
        }
    }

    #[test]
    fn convolve_binomial_unequal_p_refuses_named_match() {
        let x = Discrete::Binomial { n: 3, p: p(1, 3) };
        let y = Discrete::Binomial { n: 2, p: p(1, 2) };
        let conv = convolve(&x, &y).expect("finite support");
        assert!(
            conv.sums_to_one.is_certified(),
            "the table itself is still a valid distribution"
        );
        let matched = conv
            .matches_named
            .expect("Binomial+Binomial attempts a match");
        assert!(
            !matched.is_certified(),
            "unequal p must be refused, not silently certified"
        );
        let Trust::Uncertified(reason) = &matched.trust else {
            panic!("expected Uncertified");
        };
        assert!(reason.contains("p1 != p2"));
    }

    // ---------------------------------------------------------------
    // Convolution: Poisson + Poisson -> Poisson (WZ, all k at once)
    // ---------------------------------------------------------------

    #[test]
    fn convolve_poisson_matches_named_poisson_for_all_k() {
        let x = Discrete::Poisson(CasExpr::int(2));
        let y = Discrete::Poisson(CasExpr::int(3));
        let matched = convolve_poisson(&x, &y).expect("both concrete");
        assert!(matched.is_certified(), "{matched:?}");
    }

    #[test]
    fn convolve_poisson_symbolic_lambda_declines() {
        let x = Discrete::Poisson(CasExpr::var("l1"));
        let y = Discrete::Poisson(CasExpr::int(3));
        assert!(convolve_poisson(&x, &y).is_none());
    }

    // ---------------------------------------------------------------
    // Chebyshev / Markov bounds
    // ---------------------------------------------------------------

    #[test]
    fn chebyshev_bound_derived_from_certified_binomial_moments() {
        let d = Discrete::Binomial { n: 4, p: p(1, 2) };
        let mean = d.mean();
        let variance = d.variance();
        let bound = chebyshev_bound(&mean, &variance, &CasExpr::int(1));
        assert!(bound.is_certified());
        assert!(matches!(bound.route, Route::Derived));
        // variance/k^2 = 1/1 = 1.
        assert!(matches!(
            equal(&bound.claim, &CasExpr::int(1)),
            ZeroTest::Certified { equal: true, .. }
        ));
    }

    #[test]
    fn chebyshev_bound_propagates_uncertified_input() {
        // `Geometric(2)` has ratio `q = −1`: a genuinely divergent series, and
        // therefore an honest uncertified input rather than a contrived one.
        let d = Discrete::Geometric(CasExpr::int(2));
        let mean = d.mean(); // uncertified
        let variance = d.variance(); // uncertified
        assert!(!mean.is_certified() && !variance.is_certified());
        let bound = chebyshev_bound(&mean, &variance, &CasExpr::int(1));
        assert!(!bound.is_certified());
    }

    #[test]
    fn markov_bound_derived_from_certified_mean() {
        let d = Continuous::Exponential(CasExpr::int(2));
        let mean = d.mean();
        let bound = markov_bound(&mean, &CasExpr::int(1));
        assert!(bound.is_certified());
        assert!(matches!(bound.route, Route::Derived));
        assert!(matches!(
            equal(&bound.claim, &p(1, 2)),
            ZeroTest::Certified { equal: true, .. }
        ));
    }

    // ---------------------------------------------------------------
    // Forged certificates are refused (three distinct ways).
    // ---------------------------------------------------------------

    #[test]
    fn forged_certificates_are_refused() {
        let d = Discrete::Binomial { n: 4, p: p(1, 2) };

        // 1. Wrong claim value, correctly labeled Certified.
        let forged_value = Certificate::certified(CasExpr::int(999), Route::ExpandEqual);
        assert!(!d.verify_mean(&forged_value));

        // 2. Correct claim value, falsely labeled Certified when the fresh
        //    re-derivation would (hypothetically) decline -- modeled here by
        //    forging Certified on a value that does not match at all, since
        //    Binomial's own mean always certifies; the falsely-labeled case is
        //    instead exercised on a divergent-ratio Geometric below, whose mean
        //    is an honest decline.
        let d2 = Discrete::Geometric(CasExpr::int(2));
        let genuinely_uncertified = d2.mean();
        assert!(!genuinely_uncertified.is_certified());
        let falsely_certified =
            Certificate::certified(genuinely_uncertified.claim.clone(), Route::InfiniteSum);
        // agree() requires BOTH sides certified; the fresh re-derivation is
        // (honestly) uncertified, so verify refuses even though the claim
        // value matches exactly.
        assert!(!d2.verify_mean(&falsely_certified));

        // 3. Right value and route, wrong Certified/Uncertified mismatch the
        //    other way: a correct-but-labeled-uncertified certificate does not
        //    verify against the real (certified) one via strict equality
        //    semantics of `agree`, even though the claim values match.
        let mean = d.mean();
        let mismatched_trust =
            Certificate::uncertified(mean.claim.clone(), Route::ExpandEqual, "fabricated decline");
        assert!(!d.verify_mean(&mismatched_trust));
    }

    // ---------------------------------------------------------------
    // Mutation-guard tests: delete a specific guard, confirm exactly one
    // test fails. Documented here so the removal is reproducible; the actual
    // deletions were performed transiently against a scratch copy (never in
    // this shared worktree) and reverted -- see the lane's final report.
    // ---------------------------------------------------------------

    #[test]
    fn convolution_table_sum_guard_catches_a_bad_table() {
        // Call the REAL guard convolve() uses (table_sums_to_one), not a
        // synthetic re-derivation, on a hand-built corrupted table.
        let mut good = BTreeMap::new();
        good.insert(0i128, p(1, 2).into_const().unwrap());
        good.insert(1i128, p(1, 2).into_const().unwrap());
        assert!(table_sums_to_one(&good).unwrap().is_certified());

        let mut bad = BTreeMap::new();
        bad.insert(0i128, p(1, 2).into_const().unwrap());
        bad.insert(1i128, p(1, 3).into_const().unwrap()); // sums to 5/6, not 1
        assert!(!table_sums_to_one(&bad).unwrap().is_certified());
    }

    // ---------------------------------------------------------------
    // Symbolic parameters: certified UNDER a recorded hypothesis.
    //
    // Every test below names the guard it pins; deleting that guard kills
    // this test and (checked) no other.
    // ---------------------------------------------------------------

    /// The condition a certificate carries, rendered — the ledger row's text.
    fn conditions(certificate: &Certificate) -> String {
        certificate.hypotheses_display()
    }

    /// `Exponential(λ)` with a symbolic `λ`: mass, mean and variance all decide,
    /// each under the single condition `λ > 0`.
    #[test]
    fn exponential_symbolic_lambda_mass_mean_variance_under_positive_lambda() {
        let lambda = CasExpr::var("lam");
        let d = Continuous::Exponential(lambda.clone());

        let total = d.total_mass();
        assert!(total.is_decided(), "{total:?}");
        assert_eq!(conditions(&total), "lam > 0");
        assert_eq!(total.route, Route::ConditionalIntegrate);
        assert!(matches!(
            equal(&total.claim, &CasExpr::one()),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert_eq!(conditions(&mean), "lam > 0");
        assert!(matches!(
            equal(&mean.claim, &(CasExpr::one() / lambda.clone())),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mean(&mean));

        let variance = d.variance();
        assert_eq!(conditions(&variance), "lam > 0");
        assert!(matches!(
            equal(&variance.claim, &(CasExpr::one() / lambda.pow(2))),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_variance(&variance));
    }

    /// The headline: `M(t) = λ/(λ−t)` for a symbolic `λ` **and** a symbolic `t`,
    /// certified under `t < λ` — written by the route as `λ − t > 0`.
    #[test]
    fn exponential_symbolic_lambda_mgf_under_t_below_lambda() {
        let lambda = CasExpr::var("lam");
        let d = Continuous::Exponential(lambda.clone());
        let mgf = d.mgf("t");
        assert!(mgf.is_decided(), "{mgf:?}");
        assert!(
            !mgf.is_certified(),
            "a conditional mgf must never read as unconditional"
        );
        assert_eq!(mgf.route, Route::ConditionalIntegrate);
        assert_eq!(conditions(&mgf), "lam - t > 0");
        assert!(matches!(
            equal(&mgf.claim, &(lambda.clone() / (lambda - CasExpr::var("t")))),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    /// **The dropped-hypothesis forgery.** The claim is character-for-character
    /// the real one; only the condition is missing. `agree`'s trust-tag equality
    /// is the guard — replace it with "both are decided" and this test dies.
    #[test]
    fn an_mgf_certificate_with_the_hypothesis_dropped_is_refused() {
        let lambda = CasExpr::var("lam");
        let d = Continuous::Exponential(lambda.clone());
        let genuine = d.mgf("t");
        assert!(d.verify_mgf("t", &genuine), "the genuine one must verify");

        // 1. Same claim, same route, hypothesis deleted.
        let forged = Certificate {
            claim: genuine.claim.clone(),
            route: genuine.route,
            trust: Trust::Certified,
        };
        assert!(
            !d.verify_mgf("t", &forged),
            "`λ/(λ−t)` without `t < λ` is a false claim and must not verify"
        );

        // 2. Same claim, a *different* (weaker, and wrong) condition.
        let swapped = Certificate {
            claim: genuine.claim.clone(),
            route: genuine.route,
            trust: Trust::CertifiedUnder(vec![SignCondition::NonZero(CasExpr::var("t"))]),
        };
        assert!(!d.verify_mgf("t", &swapped));

        // 3. Right condition, wrong claim.
        let wrong_value = Certificate {
            claim: CasExpr::int(999),
            route: genuine.route,
            trust: genuine.trust.clone(),
        };
        assert!(!d.verify_mgf("t", &wrong_value));
    }

    /// `Uniform(a, b)`'s mgf, under `t ≠ 0`. The `t = 0` value `M(0) = 1` is a
    /// **removable** singularity of the closed form, and it is exactly what the
    /// recorded condition excludes: nothing in this crate decides that limit, so
    /// the certificate does not claim it.
    #[test]
    fn uniform_mgf_certifies_under_a_nonzero_t() {
        let d = Continuous::Uniform {
            a: Rational::integer(2),
            b: Rational::integer(5),
        };
        let mgf = d.mgf("t");
        assert!(mgf.is_decided(), "{mgf:?}");
        assert_eq!(conditions(&mgf), "t != 0");
        let t = CasExpr::var("t");
        let target = ((t.clone() * CasExpr::int(5)).exp() - (t.clone() * CasExpr::int(2)).exp())
            / (t * CasExpr::int(3));
        assert!(matches!(
            equal(&mgf.claim, &target),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    /// An **independent** cross-check of the uniform mgf: instantiate the
    /// symbolic claim at `t = 1` and compare with the ordinary (unconditional)
    /// `improper_integrate` of `e^{x}/(b−a)` over `[a, b]`, which is a different
    /// code path entirely (`to_univariate` with a concrete coefficient).
    #[test]
    fn the_uniform_mgf_claim_agrees_with_the_concrete_integral_at_t_equals_one() {
        let d = Continuous::Uniform {
            a: Rational::integer(2),
            b: Rational::integer(5),
        };
        let at_one = simplify(&d.mgf("t").claim.substitute("t", &CasExpr::one()));
        let integrand = (CasExpr::one() / CasExpr::int(3)) * CasExpr::var("x").exp();
        let direct = improper_integrate(
            &integrand,
            "x",
            LimitPoint::Finite(Rational::integer(2)),
            LimitPoint::Finite(Rational::integer(5)),
        )
        .expect("a concrete coefficient of x is the elementary rule's own case");
        assert!(direct.is_certified());
        assert!(
            matches!(
                equal(&at_one, &direct.value),
                ZeroTest::Certified { equal: true, .. }
            ),
            "symbolic claim at t=1: {at_one}; independent concrete integral: {}",
            direct.value
        );
    }

    /// `Normal(μ, σ²)`'s mgf for symbolic `μ` **and** symbolic `t`, with no
    /// condition at all: `σ²` is concrete, so its sign is decided, not recorded.
    #[test]
    fn normal_symbolic_mu_and_t_mgf_certifies_unconditionally() {
        let mu = CasExpr::var("mu");
        let d = Continuous::Normal {
            mu: mu.clone(),
            variance: CasExpr::Const(Rational::integer(4)),
        };
        let mgf = d.mgf("t");
        assert!(mgf.is_certified(), "{mgf:?}");
        assert!(mgf.hypotheses().is_empty());
        assert_eq!(mgf.route, Route::GaussianShift);
        let t = CasExpr::var("t");
        let target = (t.clone() * mu + CasExpr::int(4) * t.pow(2) / CasExpr::int(2)).exp();
        assert!(matches!(
            equal(&mgf.claim, &target),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    /// **Negative control.** A non-positive variance is not a Gaussian this route
    /// can integrate, and the mgf must decline rather than certify a formula that
    /// happens to be spellable. Pins `normal_mgf`'s shifted-mass check: delete it
    /// and `e^{μt − t²/2}` would come back certified for `σ² = −1`.
    #[test]
    fn normal_with_a_non_positive_variance_declines_its_mgf() {
        // The two non-positive cases fail at *different* guards, and the reason
        // string says which — which is the point of recording one.
        let reason_for = |variance: Rational| -> String {
            let d = Continuous::Normal {
                mu: CasExpr::var("mu"),
                variance: CasExpr::Const(variance),
            };
            let mgf = d.mgf("t");
            assert!(!mgf.is_decided(), "variance {variance:?}: {mgf:?}");
            // …and the whole family declines with it, so nothing downstream can
            // pick up a certified moment for an impossible distribution.
            assert!(!d.total_mass().is_decided(), "variance {variance:?}");
            match &mgf.trust {
                Trust::Uncertified(reason) => reason.clone(),
                other => panic!("expected Uncertified for variance {variance:?}: {other:?}"),
            }
        };

        // σ² = −1: the square completes fine, but the shifted Gaussian points the
        // wrong way, so there is no erf antiderivative and no total mass. Pins
        // `normal_mgf`'s shifted-mass check: delete it and `e^{μt − t²/2}` comes
        // back certified for a negative variance.
        let negative = reason_for(Rational::integer(-1));
        assert!(negative.contains("shifted Normal"), "{negative}");

        // σ² = 0: the exponent is not a Gaussian at all (its `2σ²` denominator is
        // zero), so the identity itself does not decide. Pins the square-completion
        // check, which is a different guard.
        let zero = reason_for(Rational::zero());
        assert!(zero.contains("completing the square"), "{zero}");
    }

    /// `decide_conditional` re-checks the route's own differentiate-and-check
    /// certificate. Pins that check: a `ConditionalIntegral` whose antiderivative
    /// was never proved must not certify, even when its value is the right one.
    #[test]
    fn a_conditional_integral_with_an_unproved_antiderivative_is_refused() {
        let honest = improper_integrate_conditional(
            &exponential_pdf(&CasExpr::var("lam")),
            "x",
            LimitPoint::Finite(Rational::zero()),
            LimitPoint::PosInfinity,
        )
        .expect("the symbolic-rate route");
        assert!(decide_conditional(&honest, &CasExpr::one(), "control").is_decided());

        let unproved = ConditionalIntegral {
            certificate: ZeroTest::Unknown,
            ..honest
        };
        let verdict = decide_conditional(&unproved, &CasExpr::one(), "forged");
        assert!(!verdict.is_decided(), "{verdict:?}");
        let Trust::Uncertified(reason) = &verdict.trust else {
            panic!("expected Uncertified");
        };
        assert!(reason.contains("differentiate-and-check"), "{reason}");
    }

    /// `restate_positive` flips `e < 0` to `−e > 0` and leaves the other two
    /// forms alone. Pins the `equal` check inside it: the rewrite is decided,
    /// not assumed.
    #[test]
    fn restate_positive_flips_only_a_strict_negativity() {
        let lambda = CasExpr::var("lam");
        let raw = SignCondition::Negative(CasExpr::Neg(Box::new(lambda.clone())));
        let SignCondition::Positive(flipped) = restate_positive(&raw) else {
            panic!("a strict negativity must be restated as a positivity");
        };
        assert!(matches!(
            equal(&flipped, &lambda),
            ZeroTest::Certified { equal: true, .. }
        ));
        for unchanged in [
            SignCondition::Positive(lambda.clone()),
            SignCondition::NonZero(lambda),
        ] {
            assert_eq!(restate_positive(&unchanged), unchanged);
        }
    }

    /// A derived bound inherits its inputs' conditions instead of laundering
    /// them into a bare `Certified`. Pins the union in `chebyshev_bound` /
    /// `markov_bound`.
    #[test]
    fn derived_bounds_carry_their_inputs_conditions() {
        let d = Continuous::Exponential(CasExpr::var("lam"));
        let mean = d.mean();
        let variance = d.variance();
        let chebyshev = chebyshev_bound(&mean, &variance, &CasExpr::int(2));
        assert!(chebyshev.is_decided());
        assert!(
            !chebyshev.is_certified(),
            "a bound built from conditional moments is conditional"
        );
        assert_eq!(conditions(&chebyshev), "lam > 0");
        let markov = markov_bound(&mean, &CasExpr::int(1));
        assert_eq!(conditions(&markov), "lam > 0");
        // Both moments carry the same condition; the union must record it once.
        assert_eq!(chebyshev.hypotheses().len(), 1);
    }

    /// `gosper_sum` still declines on a symbolic ratio — that measurement has
    /// not changed and is run here, not remembered. What changed is that the
    /// decline is no longer the end of the road: `infinite_sum_conditional`
    /// reaches the same summand through the geometric series, under a recorded
    /// condition. Both halves are asserted so neither can rot silently.
    #[test]
    fn the_symbolic_ratio_still_declines_in_gosper_and_is_reached_conditionally() {
        let j = CasExpr::var("j");
        let p_symbol = CasExpr::var("p");
        let ratio = CasExpr::one() - p_symbol.clone();
        let summand = p_symbol * (j.clone() * ratio.ln()).exp();
        assert!(
            crate::gosper_sum(&summand, "j").is_none(),
            "the geometric route exists because Gosper has no antidifference here"
        );
        let bare = (j.clone() * CasExpr::var("q").ln()).exp();
        assert!(crate::gosper_sum(&bare, "j").is_none());
        assert!(
            crate::infinite_sum(&summand, "j", &CasExpr::zero()).is_none(),
            "and neither does the unconditional summation API"
        );
        assert!(infinite_sum_conditional(&summand, "j", &CasExpr::zero()).is_some());
        // Positive control at a concrete ratio, so the negatives above are not an
        // empty result from a route that never fires.
        let concrete = CasExpr::rat(1, 3) * (j * CasExpr::rat(2, 3).ln()).exp();
        assert!(crate::infinite_sum(&concrete, "j", &CasExpr::zero()).is_some());
    }

    // ---------------------------------------------------------------
    // Wave four: the two symbolic-parameter families that used to decline.
    // ---------------------------------------------------------------

    fn conditions_of(cert: &Certificate) -> String {
        cert.hypotheses_display()
    }

    /// `Geometric(p)` at a **symbolic** `p`: all four quantities certify, each
    /// under `0 < p < 1` and the mgf additionally under `t < −ln(1−p)`.
    #[test]
    fn geometric_symbolic_p_certifies_all_four_under_zero_lt_p_lt_one() {
        let symbol = CasExpr::var("p");
        let d = Discrete::Geometric(symbol.clone());

        let total = d.total_mass();
        assert!(total.is_decided() && !total.is_certified(), "{total:?}");
        assert_eq!(conditions_of(&total), "p > 0 and 1 - p > 0");
        assert!(matches!(
            equal(&total.claim, &CasExpr::one()),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert_eq!(conditions_of(&mean), "p > 0 and 1 - p > 0");
        assert!(matches!(
            equal(&mean.claim, &(CasExpr::one() / symbol.clone())),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mean(&mean));

        let variance = d.variance();
        assert_eq!(conditions_of(&variance), "p > 0 and 1 - p > 0");
        assert!(matches!(
            equal(
                &variance.claim,
                &((CasExpr::one() - symbol.clone()) / symbol.clone().pow(2))
            ),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_variance(&variance));

        let mgf = d.mgf("t");
        assert!(mgf.is_decided(), "{mgf:?}");
        assert_eq!(
            conditions_of(&mgf),
            "p > 0 and 1 - p > 0 and -ln(1 - p) - t > 0"
        );
        let e = CasExpr::var("t").exp();
        let target =
            (symbol.clone() * e.clone()) / (CasExpr::one() - (CasExpr::one() - symbol) * e);
        assert!(matches!(
            equal(&mgf.claim, &target),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    /// A **concrete** `p` still certifies with no conditions at all: the route
    /// decides `|1−p| < 1` on the spot, so nothing that used to be unconditional
    /// silently became conditional.
    #[test]
    fn a_concrete_geometric_p_stays_unconditional() {
        let d = Discrete::Geometric(p(1, 3));
        for cert in [d.total_mass(), d.mean(), d.variance()] {
            assert!(cert.is_certified(), "{cert:?}");
            assert!(cert.hypotheses().is_empty());
        }
    }

    /// **Forgery control.** A `Geometric` certificate with the hypotheses
    /// dropped has a claim character-for-character identical to the genuine one
    /// and must still be refused.
    #[test]
    fn a_geometric_certificate_with_the_hypotheses_dropped_is_refused() {
        let d = Discrete::Geometric(CasExpr::var("p"));
        let genuine = d.mean();
        assert!(d.verify_mean(&genuine));
        let forged = Certificate::certified(genuine.claim.clone(), genuine.route);
        assert!(!d.verify_mean(&forged));
        // …and one that keeps only the weaker half of the pair is refused too.
        let half = Certificate::certified_under(
            genuine.claim.clone(),
            genuine.route,
            vec![SignCondition::Positive(CasExpr::var("p"))],
        );
        assert!(!d.verify_mean(&half));
    }

    /// **Guard**, pinning `restate_geometric`'s `equal` check: a condition that
    /// is not the route's own `1 − |q| > 0` for *this* `p` passes through
    /// unchanged rather than being relabelled `0 < p < 1`. Delete the check and
    /// this test dies, because the unrelated condition comes back as the pair.
    #[test]
    fn an_unrecognized_convergence_condition_is_not_relabelled() {
        let symbol = CasExpr::var("p");
        let genuine =
            SignCondition::Positive(CasExpr::one() - (CasExpr::one() - symbol.clone()).abs());
        assert_eq!(
            restate_geometric(&genuine, &symbol, None),
            vec![
                SignCondition::Positive(symbol.clone()),
                SignCondition::Positive(CasExpr::one() - symbol.clone()),
            ]
        );
        // A margin for a DIFFERENT ratio is not this distribution's condition.
        let foreign = SignCondition::Positive(CasExpr::one() - CasExpr::var("q").abs());
        assert_eq!(
            restate_geometric(&foreign, &symbol, None),
            vec![foreign.clone()]
        );
        // …and so is a condition of another kind entirely.
        let other = SignCondition::NonZero(symbol.clone());
        assert_eq!(restate_geometric(&other, &symbol, None), vec![other]);
    }

    /// `Normal(μ, σ²)` at a **symbolic** `σ²`: all four quantities certify, each
    /// under exactly `σ² > 0` and nothing else.
    #[test]
    fn normal_symbolic_variance_certifies_all_four_under_variance_positive() {
        let sigma_squared = CasExpr::var("s");
        let mu = CasExpr::var("mu");
        let d = Continuous::Normal {
            mu: mu.clone(),
            variance: sigma_squared.clone(),
        };

        let total = d.total_mass();
        assert!(total.is_decided() && !total.is_certified(), "{total:?}");
        assert_eq!(conditions_of(&total), "s > 0");
        assert!(matches!(
            equal(&total.claim, &CasExpr::one()),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert_eq!(conditions_of(&mean), "s > 0");
        assert!(matches!(
            equal(&mean.claim, &mu),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mean(&mean));

        let variance = d.variance();
        assert_eq!(conditions_of(&variance), "s > 0");
        assert!(matches!(
            equal(&variance.claim, &sigma_squared),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_variance(&variance));

        let mgf = d.mgf("t");
        assert_eq!(conditions_of(&mgf), "s > 0");
        assert_eq!(mgf.route, Route::GaussianShift);
        let t = CasExpr::var("t");
        let target = (t.clone() * mu + sigma_squared * t.pow(2) / CasExpr::int(2)).exp();
        assert!(matches!(
            equal(&mgf.claim, &target),
            ZeroTest::Certified { equal: true, .. }
        ));
        assert!(d.verify_mgf("t", &mgf));
    }

    /// **Forgery control** for the continuous side: the same claim with `σ² > 0`
    /// dropped is refused.
    #[test]
    fn a_normal_certificate_with_the_variance_hypothesis_dropped_is_refused() {
        let d = Continuous::Normal {
            mu: CasExpr::zero(),
            variance: CasExpr::var("s"),
        };
        let genuine = d.variance();
        assert!(d.verify_variance(&genuine));
        let forged = Certificate::certified(genuine.claim.clone(), genuine.route);
        assert!(!d.verify_variance(&forged));
    }

    /// **Guard**, pinning `normal_symbolic_coeff_is_the_pdf`: the normalizer is
    /// *decided* to be `1/√(2πσ²)`, not asserted. A constant off by a factor —
    /// the classic `σ` where `σ²` belongs, or a missing `2` — is refused. Make
    /// the function return `true` unconditionally and this test dies.
    #[test]
    fn the_normalizer_obligation_refuses_a_wrong_constant() {
        let s = CasExpr::var("s");
        assert!(normal_symbolic_coeff_is_the_pdf(
            &normal_symbolic_coeff(&s),
            &s
        ));
        // `√(1/σ²)/√π` — the same shape with the `2` dropped out of the rate.
        let missing_two = crate::simplify_radicals(&(CasExpr::one() / s.clone()).sqrt())
            / CasExpr::var("pi").sqrt();
        assert!(!normal_symbolic_coeff_is_the_pdf(&missing_two, &s));
        // `1/√(2πσ)` — the standard deviation where the variance belongs.
        let sigma_not_variance =
            CasExpr::one() / (CasExpr::int(2) * CasExpr::var("pi") * s.clone().sqrt()).sqrt();
        assert!(!normal_symbolic_coeff_is_the_pdf(&sigma_not_variance, &s));
    }

    /// **Guard**, pinning `restate_variance_positive`'s `equal` check: only a
    /// condition on something decided to be `1/(2σ²)` is restated as `σ² > 0`.
    #[test]
    fn a_condition_that_is_not_the_gaussian_rate_is_not_restated() {
        let s = CasExpr::var("s");
        let rate = SignCondition::Positive(normal_rate(&s));
        assert_eq!(
            restate_variance_positive(&rate, &s),
            SignCondition::Positive(s.clone())
        );
        // Not the rate: `1/σ²` is positive exactly when `σ²` is, but the guard
        // must not take that on faith — `equal(a·2σ², 1)` is what it checks.
        let not_the_rate = SignCondition::Positive(CasExpr::one() / s.clone());
        assert_eq!(
            restate_variance_positive(&not_the_rate, &s),
            not_the_rate.clone()
        );
        let negative = SignCondition::Negative(normal_rate(&s));
        assert_eq!(restate_variance_positive(&negative, &s), negative);
    }

    /// A **concrete** variance still certifies unconditionally, through the
    /// unchanged `improper_integrate` path: the symbolic route is additive, not
    /// a replacement.
    #[test]
    fn a_concrete_variance_stays_on_the_unconditional_route() {
        let d = Continuous::Normal {
            mu: CasExpr::zero(),
            variance: CasExpr::int(1),
        };
        for cert in [d.total_mass(), d.mean(), d.variance()] {
            assert!(cert.is_certified(), "{cert:?}");
            assert!(cert.hypotheses().is_empty());
            assert_eq!(cert.route, Route::ImproperIntegrate);
        }
    }
}
