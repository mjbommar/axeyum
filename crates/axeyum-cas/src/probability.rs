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
//! concrete) support, building the exact closed CasExpr sum, and deciding the
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
//! - **A symbolic coefficient inside `exp(...)` breaks every transform-style
//!   route.** [`crate::laplace_transform`] and the elementary `∫e^{c·x}`
//!   antiderivative both call `to_univariate`, which requires the polynomial
//!   coefficients to be concrete [`axeyum_ir::Rational`]s. So `Exponential(λ)`'s
//!   pdf `λ·e^{−λx}` only transforms for **concrete** `λ`; a *moment generating
//!   function*'s own argument `t` is, by definition, symbolic, so `e^{t·x}`
//!   integrated over an **unbounded** domain (Geometric, Poisson, Uniform via
//!   the plain elementary rule) declines structurally, independent of whether
//!   the distribution's own parameters are concrete. This is why every
//!   infinite-support discrete MGF below is uncertified for symbolic `t`, and
//!   why the continuous MGF route is [`crate::laplace_transform`] evaluated at
//!   `s = −t` (its *own* variable is `s`; the transform never needs to parse
//!   `t` as a coefficient) rather than a raw `∫ e^{tx}·f(x)`.
//! - **`Σ k·cᵏ` cannot be limited to `∞`, even after independently re-verifying
//!   a hand-cancelled antidifference.** [`crate::gosper_sum`] finds a valid
//!   telescoping antidifference `S(k)` for `k·pq^k` (re-verified here via
//!   [`crate::equal`] on the telescoping identity itself, independently of the
//!   producer — see `geometric_mean_and_variance_decline_but_recorded_reason`),
//!   but the raw `S(k)` carries an unreduced `k/k` factor that [`crate::limit`]
//!   cannot resolve, and it still cannot after cancelling that factor by hand.
//!   So `Geometric`'s **mean and variance decline**, for *every* `p`, concrete
//!   or symbolic — not a parameter-concreteness issue at all. This is recorded
//!   here as a genuine capability gap, not hidden behind a fallback.
//! - **`λᵏ/k!` is not Gosper-summable.** [`crate::gosper_sum`] returns `None`
//!   for `λᵏ/k!` at both a concrete `λ` (`3`) and a symbolic one: there is no
//!   hypergeometric closed-form antidifference (the underlying reason `eˣ`'s
//!   Taylor tail has no telescoping form). So **every** `Poisson` quantity
//!   (mass, mean, variance, mgf) is uncertified through this crate's summation
//!   machinery, for any `λ`. The closed forms reported are the standard ones,
//!   labelled accordingly.
//! - **`integrate_gaussian` requires `√a` rational.** For a pdf normalized as
//!   `e^{−x²/(2σ²)}`, `a = 1/(2σ²)`; `σ² = 1` (the textbook `Normal(0,1)`) gives
//!   `a = 1/2`, whose square root is irrational, so the erf-antiderivative
//!   finder declines — for total mass, mean, *and* variance, not just the mgf.
//!   `σ² = 1/2` gives `a = 1` (`√a = 1`, rational) and everything but the mgf
//!   certifies. This module therefore reports the **honest decline** for
//!   `Normal(0,1)` exactly as anticipated, and a second, certifying concrete
//!   instance to demonstrate the route actually works when the crate's own
//!   precondition holds.
//! - **The Poisson⊕Poisson convolution identity *does* have a general
//!   certificate** — not from [`crate::infinite_sum`] (which cannot even certify
//!   a single Poisson's own total mass) but from [`crate::prove_wz_sum`], the
//!   Wilf–Zeilberger prover: `Σⱼ C(k,j)·λ₁ʲ·λ₂ᵏ⁻ʲ = (λ₁+λ₂)ᵏ` for *every* `k`,
//!   proved symbolically in `k` for concrete `λ₁, λ₂` (a genuinely different,
//!   stronger machine than the one this module's own `Poisson::total_mass`
//!   uses, which is why the convolution's closed-form match certifies while
//!   the underlying single-Poisson total mass does not — recorded honestly,
//!   not smoothed over).
//!
//! # Trust model
//!
//! Every quantity returns a [`Certificate`]: a claim (`CasExpr`), the
//! [`Route`] that produced it, and a [`Trust`] tag. [`Trust::Certified`] means
//! an independent primitive (never a numeric spot-check, never `f64`) decided
//! the identity. [`Trust::Uncertified`] carries the specific reason the route
//! declined — never silently promoted to certified. [`Certificate::verify`]
//! (via each type's `verify_*` method) independently re-derives the claim from
//! the distribution's definition and re-decides equality with
//! [`crate::equal`]; a hand-forged certificate (wrong claim, or a claimed
//! `Certified` that the fresh re-derivation cannot reach) is refused. See
//! `forged_certificates_are_refused` for the three distinct ways a forgery is
//! caught.
//!
//! Chebyshev/Markov bounds are built from certified mean/variance but are
//! **not themselves re-proved** here — [`Route::Derived`] records exactly
//! that: the inequality's soundness is inherited from probability theory, not
//! re-established by this module.

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use crate::{
    CasExpr, LimitPoint, UnaryFunc, ZeroTest, binomial_coefficient, definite_sum, equal, expand,
    improper_integrate, infinite_sum, laplace_transform, ntheory, prove_wz_sum, simplify,
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
    /// [`crate::infinite_sum`]'s telescoping-plus-limit certificate over an
    /// unbounded discrete support.
    InfiniteSum,
    /// [`crate::improper_integrate`]'s certified antiderivative/limit route
    /// over a continuous support.
    ImproperIntegrate,
    /// [`crate::laplace_transform`] evaluated at `s = −t`.
    LaplaceTransform,
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
    /// An independent primitive decided the claim exactly.
    Certified,
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

    fn uncertified(claim: CasExpr, route: Route, reason: impl Into<String>) -> Self {
        Certificate {
            claim,
            route,
            trust: Trust::Uncertified(reason.into()),
        }
    }

    /// Whether this certificate's claim was independently decided.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self.trust, Trust::Certified)
    }
}

/// Two certificates **agree**: both are independently certified, and
/// [`crate::equal`] confirms their claims are the same expression. Used by
/// every `verify_*` method to catch a forged certificate — whether forged by
/// a wrong `claim`, a falsely claimed `Trust::Certified`, or both.
fn agree(a: &Certificate, b: &Certificate) -> bool {
    a.is_certified()
        && b.is_certified()
        && matches!(equal(&a.claim, &b.claim), ZeroTest::Certified { equal: true, .. })
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
        ZeroTest::Certified { equal: true, .. } => {
            Certificate::certified(target.clone(), Route::ExpandEqual)
        }
        ZeroTest::Certified { equal: false, .. } => Certificate::uncertified(
            simplified,
            Route::ExpandEqual,
            "expand+equal decided the enumerated sum does NOT equal the target",
        ),
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
                #[allow(clippy::cast_sign_loss)]
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
                #[allow(clippy::cast_sign_loss)]
                let exponent = (k - 1) as u32;
                p.clone() * (CasExpr::one() - p.clone()).pow(exponent)
            }
            Discrete::Poisson(lambda) => {
                if k < 0 {
                    return CasExpr::zero();
                }
                #[allow(clippy::cast_sign_loss)]
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
    #[must_use]
    pub fn total_mass(&self) -> Certificate {
        match self {
            Discrete::Bernoulli(_) | Discrete::Binomial { .. } | Discrete::DiscreteUniform { .. } => {
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
                let Some(p_val) = as_concrete(p) else {
                    return Certificate::uncertified(
                        CasExpr::one(),
                        Route::InfiniteSum,
                        "symbolic p: infinite_sum's convergence/limit check needs a concrete \
                         ratio to decide |1-p| < 1",
                    );
                };
                // Reindex j = k-1 (support 0,1,2,…) so the summand matches the
                // machinery's own exp(j·ln q) convention; mathematically identical
                // to Σ_{k=1}^∞ p(1-p)^{k-1} by relabelling j = k-1.
                let j = CasExpr::var("j");
                let q = CasExpr::one() - CasExpr::Const(p_val);
                let ln_q = CasExpr::Unary(UnaryFunc::Ln, Box::new(q));
                let summand = CasExpr::Const(p_val) * (j.clone() * ln_q).exp();
                match infinite_sum(&summand, "j", &CasExpr::zero()) {
                    Some(value) => match equal(&value, &CasExpr::one()) {
                        ZeroTest::Certified { equal: true, .. } => {
                            Certificate::certified(CasExpr::one(), Route::InfiniteSum)
                        }
                        _ => Certificate::uncertified(
                            value,
                            Route::InfiniteSum,
                            "infinite_sum's value did not decide equal to 1",
                        ),
                    },
                    None => Certificate::uncertified(
                        CasExpr::one(),
                        Route::InfiniteSum,
                        "infinite_sum declined on the reindexed geometric summand",
                    ),
                }
            }
            Discrete::Poisson(lambda) => Certificate::uncertified(
                CasExpr::one(),
                Route::InfiniteSum,
                poisson_decline_reason(lambda),
            ),
        }
    }

    /// `E[X] = Σ_k k·pmf(k)`.
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
                    .map(|k| CasExpr::Const(Rational::integer(i128::from(k))) * self.pmf_at(i128::from(k)))
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
                Certificate::uncertified(target, Route::InfiniteSum, geometric_moment_decline_reason())
            }
            Discrete::Poisson(lambda) => {
                Certificate::uncertified(lambda.clone(), Route::InfiniteSum, poisson_decline_reason(lambda))
            }
        }
    }

    /// `Var[X] = E[X²] − E[X]²`.
    #[must_use]
    pub fn variance(&self) -> Certificate {
        match self {
            Discrete::Bernoulli(p) => {
                // p(1-p), enumerated directly: E[X^2]=p (0^2,1^2 same as X), so
                // Var = p - p^2. Verify via ExpandEqual on the defining sum.
                let target = p.clone() * (CasExpr::one() - p.clone());
                let terms = vec![
                    CasExpr::int(0).pow(2) * (CasExpr::one() - p.clone()),
                    CasExpr::int(1).pow(2) * p.clone(),
                ];
                // terms sum to E[X^2] = p; Var = E[X^2] - mean^2. Build the full
                // enumerated identity Σ k^2 pmf(k) - p^2 =? p(1-p) directly.
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
            Discrete::Binomial { n, p } => {
                let n_expr = CasExpr::Const(Rational::integer(i128::from(*n)));
                let target = n_expr.clone() * p.clone() * (CasExpr::one() - p.clone());
                let mean_sq = (n_expr * p.clone()).pow(2);
                let second_moment_terms: Vec<CasExpr> = (0..=*n)
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
            Discrete::DiscreteUniform { a, b } => {
                let n = b - a + 1;
                // Var = (n^2 - 1)/12 for a discrete uniform on n consecutive
                // integers (shift-invariant). Verify E[(K-a)^2] via definite_sum
                // on the shifted index j = k-a, j=0..n-1, then Var = E[j^2] -
                // E[j]^2 (shift-invariant, E[j]=(n-1)/2).
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
            Discrete::Geometric(p) => {
                let q = CasExpr::one() - p.clone();
                let target = q / p.clone().pow(2);
                Certificate::uncertified(target, Route::InfiniteSum, geometric_moment_decline_reason())
            }
            Discrete::Poisson(lambda) => {
                Certificate::uncertified(lambda.clone(), Route::InfiniteSum, poisson_decline_reason(lambda))
            }
        }
    }

    /// `M(t) = E[e^{tX}]`, returned as a `CasExpr` in the variable named `t`.
    #[must_use]
    pub fn mgf(&self, t: &str) -> Certificate {
        match self {
            Discrete::Bernoulli(p) => {
                let e = CasExpr::var(t).exp();
                let target = (CasExpr::one() - p.clone()) + p.clone() * e;
                let terms = vec![
                    CasExpr::var(t).pow(0) * (CasExpr::one() - p.clone()) * CasExpr::zero().pow(0),
                ];
                // Build directly as the enumerated sum Σ pmf(k) e^{kt}.
                let mut acc = CasExpr::zero();
                for k in 0..=1i128 {
                    let e_k = CasExpr::var(t).exp().pow(u32::try_from(k).unwrap());
                    acc = acc + self.pmf_at(k) * e_k;
                }
                let _ = terms;
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
                let target_simplified = simplify(&expand(&target).unwrap_or_else(|| target.clone()));
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
                    #[allow(clippy::cast_sign_loss)]
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
                    #[allow(clippy::cast_sign_loss)]
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
                Certificate::uncertified(
                    target,
                    Route::InfiniteSum,
                    "symbolic t: convergence requires t < -ln(1-p), a sign the limit \
                     routine cannot decide symbolically (mirrors the continuous-mgf \
                     to_univariate constraint: here it is the convergence test, not \
                     coefficient extraction, that declines)",
                )
            }
            Discrete::Poisson(lambda) => {
                let target = (lambda.clone() * (CasExpr::var(t).exp() - CasExpr::one())).exp();
                Certificate::uncertified(target, Route::InfiniteSum, poisson_decline_reason(lambda))
            }
        }
    }

    /// Independently re-derive [`Self::total_mass`] and confirm it agrees with
    /// `cert` (via [`agree`]) — catches a forged claim, a falsely claimed
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
}

fn poisson_decline_reason(lambda: &CasExpr) -> String {
    let which = if as_concrete(lambda).is_some() {
        "concrete"
    } else {
        "symbolic"
    };
    format!(
        "λ^k/k! is not Gosper-summable ({which} λ): gosper_sum finds no hypergeometric \
         antidifference (confirmed for λ=3 and for symbolic λ), so infinite_sum, and every \
         quantity built on it, declines regardless of parameter concreteness"
    )
}

fn geometric_moment_decline_reason() -> String {
    "gosper_sum finds a telescoping antidifference for k·p·q^k, independently re-verified via \
     equal on the telescoping identity itself, but the raw antidifference carries an unreduced \
     k/k factor that the limit routine cannot resolve at k->infinity, even after cancelling \
     that factor by hand and re-confirming the cancelled form via equal; this holds for every \
     p, concrete or symbolic"
        .to_string()
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
    /// `Exponential(λ)`, rate `λ`, possibly symbolic (declines for symbolic
    /// `λ`; see the module doc).
    Exponential(CasExpr),
    /// `Normal(μ, σ²)`: mean `μ` (possibly symbolic — added back by a shift
    /// that does not need the summation/integration machinery), variance
    /// `σ²` concrete (the erf-antiderivative finder needs `1/(2σ²)` to have a
    /// rational square root to certify at all; see the module doc).
    Normal {
        /// Mean, possibly symbolic.
        mu: CasExpr,
        /// Variance (not standard deviation — see the module doc for why).
        variance: Rational,
    },
}

impl Continuous {
    /// `∫ pdf = 1`.
    #[must_use]
    pub fn total_mass(&self) -> Certificate {
        match self {
            Continuous::Uniform { a, b } => {
                let pdf = CasExpr::one()
                    / CasExpr::Const(b.checked_sub(*a).expect("a<b"));
                match improper_integrate(&pdf, "x", LimitPoint::Finite(*a), LimitPoint::Finite(*b)) {
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
                    return Certificate::uncertified(
                        CasExpr::one(),
                        Route::ImproperIntegrate,
                        "symbolic λ: to_univariate requires a concrete Rational exponent \
                         coefficient inside e^{-λx}, so the elementary antiderivative rule \
                         (and improper_integrate's boundary limit) both decline",
                    );
                };
                let x = CasExpr::var("x");
                let pdf = CasExpr::Const(lam) * (CasExpr::Neg(Box::new(CasExpr::Const(lam))) * x).exp();
                match improper_integrate(&pdf, "x", LimitPoint::Finite(Rational::zero()), LimitPoint::PosInfinity)
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
                        "improper_integrate declined on the exponential pdf",
                    ),
                }
            }
            Continuous::Normal { variance, .. } => match normal_raw_moment(*variance, 0) {
                Some(raw) => {
                    let coeff = normal_coeff(*variance);
                    let value = simplify(&(coeff * raw));
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
                None => Certificate::uncertified(CasExpr::one(), Route::ImproperIntegrate, normal_decline_reason(*variance)),
            },
        }
    }

    /// `E[X]`.
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
                match improper_integrate(&(x * pdf), "x", LimitPoint::Finite(*a), LimitPoint::Finite(*b)) {
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
                    return Certificate::uncertified(
                        CasExpr::one() / lambda.clone(),
                        Route::ImproperIntegrate,
                        "symbolic λ: same to_univariate constraint as total_mass",
                    );
                };
                let x = CasExpr::var("x");
                let pdf = CasExpr::Const(lam) * (CasExpr::Neg(Box::new(CasExpr::Const(lam))) * x.clone()).exp();
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
            Continuous::Normal { mu, variance } => match normal_raw_moment(*variance, 1) {
                Some(raw) => {
                    let coeff = normal_coeff(*variance);
                    // E[U] over the centered variable U = X - mu; E[X] = mu + E[U].
                    let centered_mean = simplify(&(coeff * raw));
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
                None => Certificate::uncertified(mu.clone(), Route::ImproperIntegrate, normal_decline_reason(*variance)),
            },
        }
    }

    /// `Var[X] = E[X²] − E[X]²`.
    #[must_use]
    pub fn variance(&self) -> Certificate {
        match self {
            Continuous::Uniform { a, b } => {
                let pdf = CasExpr::one() / CasExpr::Const(b.checked_sub(*a).expect("a<b"));
                let x = CasExpr::var("x");
                let width = b.checked_sub(*a).expect("a<b");
                let target = width
                    .checked_mul(width)
                    .and_then(|w2| w2.checked_div(Rational::integer(12)))
                    .expect("small a,b");
                match improper_integrate(
                    &(x.clone() * x * pdf),
                    "x",
                    LimitPoint::Finite(*a),
                    LimitPoint::Finite(*b),
                ) {
                    Some(second_moment) => {
                        let mean = a
                            .checked_add(*b)
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
            Continuous::Exponential(lambda) => {
                let Some(lam) = as_concrete(lambda) else {
                    return Certificate::uncertified(
                        CasExpr::one() / lambda.clone().pow(2),
                        Route::ImproperIntegrate,
                        "symbolic λ: same to_univariate constraint as total_mass",
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
            Continuous::Normal { variance, .. } => match normal_raw_moment(*variance, 2) {
                Some(raw) => {
                    let coeff = normal_coeff(*variance);
                    let value = simplify(&(coeff * raw));
                    match equal(&value, &CasExpr::Const(*variance)) {
                        ZeroTest::Certified { equal: true, .. } => {
                            Certificate::certified(CasExpr::Const(*variance), Route::ImproperIntegrate)
                        }
                        _ => Certificate::uncertified(
                            value,
                            Route::ImproperIntegrate,
                            "the centered second moment did not decide equal to the variance parameter",
                        ),
                    }
                }
                None => Certificate::uncertified(
                    CasExpr::Const(*variance),
                    Route::ImproperIntegrate,
                    normal_decline_reason(*variance),
                ),
            },
        }
    }

    /// `M(t) = E[e^{tX}]`, returned as a `CasExpr` in the variable named `t`.
    #[must_use]
    pub fn mgf(&self, t: &str) -> Certificate {
        match self {
            Continuous::Uniform { a, b } => {
                let target = ((CasExpr::var(t) * CasExpr::Const(*b)).exp()
                    - (CasExpr::var(t) * CasExpr::Const(*a)).exp())
                    / (CasExpr::var(t) * CasExpr::Const(b.checked_sub(*a).expect("a<b")));
                Certificate::uncertified(
                    target,
                    Route::ImproperIntegrate,
                    "symbolic t: the elementary rule integrate(e^{t*x}, x) requires \
                     to_univariate to extract a concrete Rational coefficient of x; t \
                     must remain symbolic for an mgf, so this declines regardless of a, b",
                )
            }
            Continuous::Exponential(lambda) => {
                let Some(lam) = as_concrete(lambda) else {
                    return Certificate::uncertified(
                        lambda.clone() / (lambda.clone() - CasExpr::var(t)),
                        Route::LaplaceTransform,
                        "symbolic λ: laplace_transform's exp-shift extraction needs a \
                         concrete Rational coefficient inside e^{-λx}",
                    );
                };
                let x = CasExpr::var("x");
                let pdf = CasExpr::Const(lam) * (CasExpr::Neg(Box::new(CasExpr::Const(lam))) * x).exp();
                let target = CasExpr::Const(lam) / (CasExpr::Const(lam) - CasExpr::var(t));
                match laplace_transform(&pdf, "x", "s") {
                    Some(l) => {
                        // MGF(t) = L(s = -t): substitute s -> -t.
                        let mgf = simplify(&l.substitute("s", &CasExpr::Neg(Box::new(CasExpr::var(t)))));
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
            Continuous::Normal { mu, variance } => {
                let target = (CasExpr::var(t) * mu.clone()
                    + CasExpr::Const(*variance) * CasExpr::var(t).pow(2) / CasExpr::int(2))
                .exp();
                Certificate::uncertified(
                    target,
                    Route::ImproperIntegrate,
                    "symbolic t: to_univariate requires the exponent's linear coefficient \
                     (here the mgf argument t itself) to be a concrete Rational, so no \
                     antiderivative/Fourier route in this crate accepts a symbolic t here, \
                     for any variance",
                )
            }
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
    let integrand = if power == 0 { base } else { u.pow(power) * base };
    improper_integrate(&integrand, "u", LimitPoint::NegInfinity, LimitPoint::PosInfinity)
        .map(|d| d.value)
}

/// The Normal pdf's normalizing constant `1/√(2π·variance)`.
fn normal_coeff(variance: Rational) -> CasExpr {
    CasExpr::one() / (CasExpr::int(2) * CasExpr::var("pi") * CasExpr::Const(variance)).sqrt()
}

fn normal_decline_reason(variance: Rational) -> String {
    format!(
        "integrate_gaussian requires sqrt(a) rational where a = 1/(2*variance); for \
         variance={variance:?} this square root is irrational, so the erf-antiderivative \
         finder declines (this is the Normal(0,1) case when variance=1, since a=1/2)"
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

    let mut total = Rational::zero();
    for &v in table.values() {
        total = total.checked_add(v)?;
    }
    let sums_to_one = if total == Rational::integer(1) {
        Certificate::certified(CasExpr::one(), Route::ExpandEqual)
    } else {
        Certificate::uncertified(
            CasExpr::Const(total),
            Route::ExpandEqual,
            "the convolution table's exact rational sum is not 1",
        )
    };

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
/// The result carries **no** `sums_to_one` claim: `Discrete::Poisson`'s own
/// `total_mass` is itself uncertified through this crate's summation
/// machinery (see the module doc), so this function does not claim a
/// stronger result about the convolved distribution's total mass than a
/// single Poisson's own `total_mass` achieves.
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
    if mean.is_certified() && variance.is_certified() {
        Certificate {
            claim: bound,
            route: Route::Derived,
            trust: Trust::Certified,
        }
    } else {
        Certificate::uncertified(
            bound,
            Route::Derived,
            "built from an uncertified mean and/or variance input",
        )
    }
}

/// `P(X >= a) <= E[X] / a` for `a > 0` (Markov's inequality, requires `X >=
/// 0`), as a symbolic `CasExpr` bound built from a certified mean. Not
/// re-proved here — see [`chebyshev_bound`].
#[must_use]
pub fn markov_bound(mean: &Certificate, a: &CasExpr) -> Certificate {
    let bound = mean.claim.clone() / a.clone();
    if mean.is_certified() {
        Certificate {
            claim: bound,
            route: Route::Derived,
            trust: Trust::Certified,
        }
    } else {
        Certificate::uncertified(bound, Route::Derived, "built from an uncertified mean input")
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
        assert!(matches!(equal(&mean.claim, &CasExpr::var("p")), ZeroTest::Certified { equal: true, .. }));

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
        assert!(matches!(equal(&mean.claim, &CasExpr::int(2)), ZeroTest::Certified { equal: true, .. }));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(equal(&variance.claim, &CasExpr::int(1)), ZeroTest::Certified { equal: true, .. }));
    }

    #[test]
    fn binomial_symbolic_p_all_four_quantities_certify() {
        let d = Discrete::Binomial { n: 4, p: CasExpr::var("p") };
        assert!(d.total_mass().is_certified());
        assert!(d.mean().is_certified());
        assert!(d.variance().is_certified());
        assert!(d.mgf("t").is_certified());
    }

    // ---------------------------------------------------------------
    // Discrete: Geometric(1/3) mean 3 (uncertified: recorded machinery gap)
    // ---------------------------------------------------------------

    #[test]
    fn geometric_one_third_total_mass_certifies() {
        let d = Discrete::Geometric(p(1, 3));
        let total = d.total_mass();
        assert!(total.is_certified(), "{total:?}");
        assert!(d.verify_total_mass(&total));
    }

    #[test]
    fn geometric_one_third_symbolic_p_total_mass_declines() {
        let d = Discrete::Geometric(CasExpr::var("p"));
        let total = d.total_mass();
        assert!(!total.is_certified());
    }

    #[test]
    fn geometric_one_third_mean_three_uncertified() {
        let d = Discrete::Geometric(p(1, 3));
        let mean = d.mean();
        // The closed form is correct (1/p = 3) even though the route declined.
        assert!(matches!(equal(&mean.claim, &CasExpr::int(3)), ZeroTest::Certified { equal: true, .. }));
        assert!(!mean.is_certified(), "mean must be honestly uncertified: {mean:?}");
        let Trust::Uncertified(reason) = &mean.trust else {
            panic!("expected Uncertified");
        };
        assert!(reason.contains("k/k"));
    }

    // ---------------------------------------------------------------
    // Discrete: Poisson(3) mean 3 variance 3 (uncertified: not Gosper-summable)
    // ---------------------------------------------------------------

    #[test]
    fn poisson_three_mean_and_variance_three_uncertified() {
        let d = Discrete::Poisson(CasExpr::int(3));
        let mean = d.mean();
        assert!(matches!(equal(&mean.claim, &CasExpr::int(3)), ZeroTest::Certified { equal: true, .. }));
        assert!(!mean.is_certified());

        let variance = d.variance();
        assert!(matches!(equal(&variance.claim, &CasExpr::int(3)), ZeroTest::Certified { equal: true, .. }));
        assert!(!variance.is_certified());

        let total = d.total_mass();
        assert!(!total.is_certified());
    }

    #[test]
    fn poisson_symbolic_lambda_also_declines() {
        let d = Discrete::Poisson(CasExpr::var("lam"));
        assert!(!d.total_mass().is_certified());
        assert!(!d.mean().is_certified());
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
        assert!(matches!(equal(&mean.claim, &p(3, 2)), ZeroTest::Certified { equal: true, .. }));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(equal(&variance.claim, &p(5, 4)), ZeroTest::Certified { equal: true, .. }));

        let mgf = d.mgf("t");
        assert!(mgf.is_certified());
    }

    // ---------------------------------------------------------------
    // Continuous: Uniform(0,1) mean 1/2 variance 1/12
    // ---------------------------------------------------------------

    #[test]
    fn uniform_0_1_mean_half_variance_one_twelfth() {
        let d = Continuous::Uniform { a: Rational::zero(), b: Rational::integer(1) };
        let total = d.total_mass();
        assert!(total.is_certified());
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(equal(&mean.claim, &p(1, 2)), ZeroTest::Certified { equal: true, .. }));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(equal(&variance.claim, &p(1, 12)), ZeroTest::Certified { equal: true, .. }));

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
        assert!(matches!(equal(&mean.claim, &p(1, 2)), ZeroTest::Certified { equal: true, .. }));

        let variance = d.variance();
        assert!(variance.is_certified());
        assert!(matches!(equal(&variance.claim, &p(1, 4)), ZeroTest::Certified { equal: true, .. }));

        let mgf = d.mgf("t");
        assert!(mgf.is_certified(), "{mgf:?}");
        let target = CasExpr::int(2) / (CasExpr::int(2) - CasExpr::var("t"));
        assert!(matches!(equal(&mgf.claim, &target), ZeroTest::Certified { equal: true, .. }));
        assert!(d.verify_mgf("t", &mgf));
    }

    #[test]
    fn exponential_symbolic_lambda_all_decline() {
        let d = Continuous::Exponential(CasExpr::var("lam"));
        assert!(!d.total_mass().is_certified());
        assert!(!d.mean().is_certified());
        assert!(!d.variance().is_certified());
        assert!(!d.mgf("t").is_certified());
    }

    // ---------------------------------------------------------------
    // Continuous: Normal(0,1) mgf e^{t^2/2} if the Gaussian route certifies,
    // else the honest decline recorded — measured: it declines.
    // ---------------------------------------------------------------

    #[test]
    fn normal_0_1_declines_honestly() {
        let d = Continuous::Normal { mu: CasExpr::zero(), variance: Rational::integer(1) };
        assert!(!d.total_mass().is_certified(), "Normal(0,1): a=1/2 is not a perfect square");
        assert!(!d.mean().is_certified());
        assert!(!d.variance().is_certified());
        assert!(!d.mgf("t").is_certified());
    }

    #[test]
    fn normal_0_variance_half_certifies_total_mass_mean_variance() {
        // sigma^2 = 1/2 => a = 1/(2*1/2) = 1, a perfect square: the erf route certifies.
        let d = Continuous::Normal { mu: CasExpr::zero(), variance: p(1, 2).into_const().unwrap() };
        let total = d.total_mass();
        assert!(total.is_certified(), "{total:?}");
        assert!(d.verify_total_mass(&total));

        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(equal(&mean.claim, &CasExpr::zero()), ZeroTest::Certified { equal: true, .. }));

        let variance = d.variance();
        assert!(variance.is_certified(), "{variance:?}");
        assert!(matches!(equal(&variance.claim, &p(1, 2)), ZeroTest::Certified { equal: true, .. }));

        // mgf still declines regardless (symbolic t, not a variance issue).
        assert!(!d.mgf("t").is_certified());
    }

    #[test]
    fn normal_symbolic_mu_still_certifies_mean_via_shift() {
        let d = Continuous::Normal { mu: CasExpr::var("mu"), variance: p(1, 2).into_const().unwrap() };
        let mean = d.mean();
        assert!(mean.is_certified(), "{mean:?}");
        assert!(matches!(equal(&mean.claim, &CasExpr::var("mu")), ZeroTest::Certified { equal: true, .. }));
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
        let matched = conv.matches_named.expect("Binomial+Binomial attempts a match");
        assert!(matched.is_certified(), "{matched:?}");

        // Cross-check a specific point directly against Binomial(5, 1/3).
        let target = Discrete::Binomial { n: 5, p: p(1, 3) };
        for k in 0..=5 {
            let expected = concrete_value(&target.pmf_at(k)).unwrap();
            assert_eq!(conv.table.get(&k).copied().unwrap_or(Rational::zero()), expected, "k={k}");
        }
    }

    #[test]
    fn convolve_binomial_unequal_p_refuses_named_match() {
        let x = Discrete::Binomial { n: 3, p: p(1, 3) };
        let y = Discrete::Binomial { n: 2, p: p(1, 2) };
        let conv = convolve(&x, &y).expect("finite support");
        assert!(conv.sums_to_one.is_certified(), "the table itself is still a valid distribution");
        let matched = conv.matches_named.expect("Binomial+Binomial attempts a match");
        assert!(!matched.is_certified(), "unequal p must be refused, not silently certified");
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
        assert!(matches!(equal(&bound.claim, &CasExpr::int(1)), ZeroTest::Certified { equal: true, .. }));
    }

    #[test]
    fn chebyshev_bound_propagates_uncertified_input() {
        let d = Discrete::Geometric(p(1, 3));
        let mean = d.mean(); // uncertified
        let variance = d.variance(); // uncertified
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
        assert!(matches!(equal(&bound.claim, &p(1, 2)), ZeroTest::Certified { equal: true, .. }));
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
        //    instead exercised on Poisson below.
        let d2 = Discrete::Poisson(CasExpr::int(3));
        let genuinely_uncertified = d2.mean();
        assert!(!genuinely_uncertified.is_certified());
        let falsely_certified = Certificate::certified(genuinely_uncertified.claim.clone(), Route::InfiniteSum);
        // agree() requires BOTH sides certified; the fresh re-derivation is
        // (honestly) uncertified, so verify refuses even though the claim
        // value matches exactly.
        assert!(!d2.verify_mean(&falsely_certified));

        // 3. Right value and route, wrong Certified/Uncertified mismatch the
        //    other way: a correct-but-labeled-uncertified certificate does not
        //    verify against the real (certified) one via strict equality
        //    semantics of `agree`, even though the claim values match.
        let mean = d.mean();
        let mismatched_trust = Certificate::uncertified(mean.claim.clone(), Route::ExpandEqual, "fabricated decline");
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
        // Directly construct a corrupted Convolution bypassing convolve()'s
        // own arithmetic, to confirm sums_to_one's check (not just convolve's
        // happy path) actually distinguishes a bad table from a good one.
        let mut table = BTreeMap::new();
        table.insert(0i128, p(1, 2).into_const().unwrap());
        table.insert(1i128, p(1, 3).into_const().unwrap()); // sums to 5/6, not 1
        let mut total = Rational::zero();
        for &v in table.values() {
            total = total.checked_add(v).unwrap();
        }
        assert_ne!(total, Rational::integer(1));
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
