//! Certified enclosures for the **integral-defined** heads, for a symbolic
//! exponent, and for **definite integrals** by a certified quadrature
//! (math-department file 13, Next Ten item **2**, wave three).
//!
//! Same contract as [`crate::enclosure`] and [`crate::enclosure_special`]:
//! exact `BigRational` endpoints, no `f64` anywhere, a truncation order and an
//! **exact** remainder bound recorded per step, and a verifier that recomputes
//! the bound from `(head, inputs, order)` rather than reading it. Determinism
//! is by construction: every kernel here is a pure function of its argument and
//! its order, and every map is a [`BTreeMap`].
//!
//! # The heads added here
//!
//! Every one is `f(x) = ∫₀ˣ g` for an elementary `g`, so every one is a power
//! series with an integrated coefficient — and the interesting part is not the
//! series but **which** tail bound applies and **from which index**. An
//! alternating-series bound is only valid once the terms are actually falling;
//! a geometric majorant is only valid once the ratio is actually below one.
//! Both indices are computed here in exact rational arithmetic and the module
//! declines an order below them, exactly as `erf` and `J_n` do in
//! [`crate::enclosure_special`].
//!
//! | head | series | remainder bound | hypothesis |
//! |---|---|---|---|
//! | `Si` | `Σ (−1)^k x^(2k+1)/((2k+1)·(2k+1)!)` | alternating: the first omitted term at `a = max abs x` | terms fall from the least `k` with `a²(2k+1) <= (2k+2)(2k+3)²`, computed exactly; the module declines a lower order |
//! | `Shi` | the same without the sign | geometric: `t_(n+1)/(1 − R)`, `R` the exact ratio at index `n+1` | `R < 1/2`; the ratio is decreasing in `k`, so the ratio at `n+1` dominates the whole tail |
//! | `Ci` | `γ + ln x + Σ_(k>=1) (−1)^k x^(2k)/(2k·(2k)!)` | alternating, plus the `γ` and `ln` enclosures | `x > 0`; terms fall from the least `k` with `2k·a² <= (2k+1)(2k+2)²` |
//! | `Chi` | `γ + ln x + Σ_(k>=1) x^(2k)/(2k·(2k)!)` | geometric, as `Shi` | `x > 0`, `R < 1/2` |
//! | `Ei` | `γ + ln abs(x) + Σ_(k>=1) x^k/(k·k!)` | geometric with `R = a/(n+2)`, since `abs(t_(k+1)/t_k) = a·k/(k+1)² <= a/(k+1)` | `0` not in the argument (`Ei` has a logarithmic singularity there); `R < 1/2` |
//! | `li` | `li x = Ei(ln x)` | the composed `ln` and `Ei` bounds | `x > 0` and `1` not in the argument (`li` diverges at `1`) |
//! | Fresnel `C` | `Σ (−1)^k (π/2)^(2k) x^(4k+1)/((2k)!(4k+1))` | alternating, the index and the tail both evaluated at the **upper** endpoint of the certified `π` and at `a` | the ratio grows with `π/2` and with `a`, so bounding both above is sufficient |
//! | Fresnel `S` | `Σ (−1)^k (π/2)^(2k+1) x^(4k+3)/((2k+1)!(4k+3))` | as Fresnel `C` | as Fresnel `C` |
//! | `asin` | `Σ C(2k,k) z^(2k+1)/(4^k(2k+1))` for `abs(z) <= 1/2` | geometric: `t_(n+1)/(1 − z²)`, since `t_(k+1)/t_k = z²(2k+1)²/((2k+2)(2k+3)) < z²` | `abs(z) <= 3/4`; beyond `1/2` the argument is reduced first (below) |
//! | `acos` | `π/2 − asin x` | the `asin` and `π` bounds | `abs(x) <= 1` |
//! | `asinh` | `sign(x)·ln(abs(x) + √(x²+1))` — **no new series** | the `ln` and `√` bounds | none; the identity is exact on all of `ℝ` |
//! | `acosh` | `ln(x + √(x²−1))` — no new series | the `ln` and `√` bounds | `x >= 1` |
//!
//! ## Argument reduction, and where it is refused
//!
//! - **`asin` and `acos`** converge slowly near `±1` (the series ratio is
//!   `z²`), so `abs(x) > 1/2` is reduced by the exact half-angle identity
//!   `asin x = π/2 − 2·asin √((1−x)/2)`, whose argument is at most `1/2`
//!   for every `x` in `[1/2, 1]`. One level of recursion, never more.
//! - **`Si`, `Ci`, `Ei`, `Shi`, `Chi`, Fresnel `S`/`C`** have **no** rational
//!   argument reduction: the addition formulae for these functions are not
//!   elementary. Their Maclaurin series stay *sound* at any magnitude — the
//!   coefficients are exact rationals, so there is no cancellation error, only
//!   growth — but the order and the numerator size both grow like `a²`, so
//!   past [`SERIES_MAGNITUDE_LIMIT`] the module declines with
//!   [`DeclineReason::ResourceLimit`] rather than grinding. That is an honest
//!   decline, not an asymptotic bound: the asymptotic expansions of `Si` and
//!   `Ci` are divergent and their error terms need a separate justification
//!   this wave does not attempt.
//!
//! # Euler's constant
//!
//! `Ci`, `Chi` and `Ei` all carry `γ`, so `γ` itself needs a certified route.
//! [`euler_gamma`] uses **Euler–Maclaurin on `f(t) = 1/t`**:
//!
//! ```text
//! γ = H_(n−1) − ln n + 1/(2n) + Σ_(j=1)^m B_(2j)/(2j·n^(2j)) + R,
//! abs(R) <= abs(B_(2m))/(2m·n^(2m)).
//! ```
//!
//! The bound is the Euler–Maclaurin remainder
//! `R = (−1)^(m+1)·∫_n^∞ (B_(2m)({t})/(2m)!)·f^((2m))(t) dt` together with the
//! classical `abs(B_(2m)({t})) <= abs(B_(2m))` on `[0,1]` for even index
//! (DLMF 24.9.5; Abramowitz–Stegun 23.1.15) and
//! `f^((2m))(t) = (2m)!/t^(2m+1)`. Nothing about it is asymptotic hand-waving —
//! it is an integral of a bounded function against an explicitly integrable
//! one. The harmonic sum is exact, `ln n` goes through the parent module's
//! [`ln_point`], and the Bernoulli numbers come from
//! [`crate::enclosure_special::bernoulli_table`].
//!
//! `n = clamp(order, 16, 256)` and `m = clamp(order, 1, 48)`. The anchor is
//! capped because the exact `H_(n−1)` denominator grows like `e^n`, and the
//! term count because `abs(B_(2m))` grows factorially; together they put a
//! **ceiling of about `2^(−530)`** on `γ`, which is the accuracy ceiling of
//! `Ci`, `Chi` and `Ei` as well. A request beyond it declines. Results are
//! memoised per order in a [`BTreeMap`] behind a mutex — a pure function of
//! `order`, so the cache changes cost and never the value.
//!
//! # Symbolic exponents
//!
//! [`symbolic_power`] builds `x^y` as `exp(y·ln x)` — no new head at all, just
//! the two the parent module already certifies, so the evidence and the
//! verifier are the existing ones. The exponent may be any expression,
//! including a bound variable over an interval; the **base** must enclose to a
//! strictly positive interval. [`enclose_symbolic_power`] encloses the base
//! first so a non-positive one declines with a reason naming `pow`, rather
//! than with the `ln` domain error the raw composition would give.
//!
//! # Definite integrals
//!
//! [`enclose_integral`] encloses `∫_a^b f` for any integrand the module can
//! enclose, with `a` and `b` themselves **intervals** — so `∫_0^π sin` is
//! expressible with `π` supplied as its own certified enclosure.
//!
//! The core `[A, B]` is the dyadic shrink of `[a.hi, b.lo]`; it is cut into
//! `2^level` panels, and the two slivers left over — from the uncertainty in
//! `a` and `b` and from the dyadic rounding — are bounded by
//! `width · sup abs(f)` over a box containing them. Every partition point and
//! every midpoint is dyadic, which is what keeps the exact-rational kernels out
//! of the cost blow-up the previous wave measured: an endpoint carried straight
//! from a certified `π` has a two-thousand-bit denominator, and a series kernel
//! raising that to the 65th power is the failure mode
//! [`crate::enclosure_special`] documents.
//!
//! Two rules, both with an explicit error term:
//!
//! | rule | panel enclosure | error term | hypothesis |
//! |---|---|---|---|
//! | [`QuadratureRule::Simpson`] | `(w/6)(F(u) + 4F(m) + F(v)) ± (w^5/2880)·M_4` | `M_4 >= sup abs(f⁗)` on the panel, from `f.differentiate_n(var, 4)` enclosed over the panel | `f` is four times continuously differentiable on the panel — which the enclosure of `f⁗` **witnesses**: a finite interval for `f⁗` over the closed panel is exactly the statement that bounds the classical Simpson error `−(w^5/2880)·f⁗(ξ)` |
//! | [`QuadratureRule::Box`] | `w · F([u, v])` | none — the enclosure of `f` over the panel is the whole bound | `f` merely enclosable; always sound, converges linearly, used when `f⁗` cannot be enclosed |
//!
//! Simpson is tried first and the module falls back to the box rule per
//! request, never per panel, so the certificate names one rule.
//!
//! # What this module still cannot do
//!
//! - **Complex arguments.** Everything here is real; `Ci` and `Chi` of a
//!   negative argument, and `asin` outside `[−1, 1]`, are domain declines, not
//!   continuations.
//! - **Improper integrals.** `a` and `b` must be finite and `f` must be
//!   enclosable on the closed interval, so `∫_0^1 ln x`, `∫_0^∞ e^(−x)` and
//!   any integrand with an interior pole decline —
//!   [`DeclineReason::IntegrandNotEnclosable`] names the panel.
//! - **Multivariate integrals.** One variable of integration, one dimension.
//! - **`atanh` as a head.** [`UnaryFunc`] has no `Atanh` variant and this wave
//!   may not add one, so [`atanh_expr`] builds the exact identity
//!   `atanh x = (1/2)·ln((1+x)/(1−x))` from the certified `ln` instead. It is
//!   a constructor, not a head: the evidence names `Ln`, `Div` and `Mul`.
//! - **`Si`, `Ci`, `Ei`, `Shi`, `Chi`, Fresnel beyond
//!   [`SERIES_MAGNITUDE_LIMIT`]**, and `γ` beyond about `2^(−530)`.
//!
//! # Cost
//!
//! In the cost table on [`crate::enclosure`]. `cost_table_wave_three`
//! regenerates it; it is **ADVISORY ONLY** — a shared, loaded host and a single
//! unpinned run per row.

use crate::enclosure::{
    BigInterval, DeclineReason, bi, bi_u64, br, enclose_fixed_order, enclose_with_reason,
    from_rational, ln_point, pi_enclosure, pow2, rmax,
};
use crate::enclosure_special::{
    bernoulli_table, coarsen, dyadic_ceil, dyadic_floor, grid_bits, ln_large, nth_root_point,
};
use crate::interval_arith::Interval;
use crate::{CasExpr, UnaryFunc};
use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

/// The magnitude past which the integral-defined heads decline.
///
/// Their Maclaurin series stay sound at any magnitude — exact rational
/// coefficients, so growth but no cancellation error — while the order needed
/// grows like `a²` and the numerators like `a^(2·order)`. Past this the module
/// declines with [`DeclineReason::ResourceLimit`] instead of grinding.
pub const SERIES_MAGNITUDE_LIMIT: i64 = 20;

/// The largest number of Euler–Maclaurin correction pairs used for `γ`.
///
/// `abs(B_(2m))` grows factorially, so the remainder `abs(B_(2m))/(2m·n^(2m))`
/// shrinks only while `2m` stays below about `π·n`. With the anchor cap below
/// this keeps the truncation on the shrinking side at every order.
const EULER_TERMS_CAP: u32 = 48;

/// The largest Euler–Maclaurin anchor `n` used for `γ`.
///
/// `H_(n−1)` is formed exactly and its denominator is `lcm(1..n−1)`, which
/// grows like `e^n`; 256 keeps that near 370 bits.
const EULER_ANCHOR_CAP: u32 = 256;

/// The most panel-doubling refinements [`enclose_integral`] performs before
/// declining, so a pathological integrand stops rather than grinds.
const MAX_REFINEMENTS: u32 = 12;

/// The truncation order [`enclose_symbolic_power`] probes the base at.
///
/// Only the sign of the base's enclosure is read, so the order need only be
/// high enough that a genuinely positive base does not enclose down to zero.
const BASE_PROBE_ORDER: u32 = 16;

/// The search cap for a monotonicity or ratio index, matching the parent
/// modules' `SHIFT_CAP`.
const INDEX_CAP: u32 = 4096;

/// The truncation order used for the **fourth-derivative bound** of a Simpson
/// panel, independent of the order used for the integrand itself.
///
/// The derivative enclosure is only ever consumed as a magnitude — it enters
/// the error term as `sup abs(f⁗)` — so evaluating it to the integrand's own
/// accuracy is pure waste, and it is the dominant cost of a panel: measured
/// 2026-09-05 in a debug build, `∫₀¹e^(−x²)` at precision 24 spent most of its
/// 6.8 s inside the fourth derivative of `exp(−x²)`, whose folded tree carries
/// several `exp` nodes. A fixed low order is deterministic, so the verifier
/// reproduces it exactly, and a looser bound costs at most one more refinement
/// level.
const DERIVATIVE_ORDER: u32 = 8;

/// Round an accumulating series interval **outward** onto the dyadic grid for
/// `order`.
///
/// The single most important line in this module for cost. Every loop below
/// multiplies an interval by another interval `order` times, and an exact
/// rational endpoint grows by the *sum* of the factors' bit lengths at every
/// step: the Fresnel coefficient is `(π/2)^(2k)`, and a certified `π` at order
/// 16 already has 360-bit endpoints, so the coefficient at `k = 32` carries
/// twenty-three thousand bits and `num-rational`'s per-operation `gcd`
/// dominates everything. Measured 2026-09-05 in a debug build, `FresnelC(1)` at
/// precision 50 took **6.06 s** before this rounding and milliseconds after.
///
/// It is sound for the same reason [`crate::enclosure_special`]'s `coarsen` is:
/// the result **contains** the argument, so substituting it anywhere an
/// enclosure is wanted loses accuracy and never validity. The grid
/// (`2·order + 96` bits) is far finer than any truncation tail at that order,
/// so it is never what limits the answer.
fn round_series(x: &BigInterval, order: u32) -> BigInterval {
    coarsen(x, grid_bits(order))
}

// ---------------------------------------------------------------------------
// Euler's constant.
// ---------------------------------------------------------------------------

/// The memo table for [`euler_gamma`], keyed by order.
fn gamma_cache() -> &'static Mutex<BTreeMap<u32, BigInterval>> {
    static CACHE: OnceLock<Mutex<BTreeMap<u32, BigInterval>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(BTreeMap::new()))
}

/// A certified enclosure of **Euler's constant** `γ` at a truncation order.
///
/// Euler–Maclaurin on `f(t) = 1/t`, as derived in the module documentation:
///
/// ```text
/// γ = H_(n−1) − ln n + 1/(2n) + Σ_(j=1)^m B_(2j)/(2j·n^(2j)) + R,
/// abs(R) <= abs(B_(2m))/(2m·n^(2m))
/// ```
///
/// with `n = clamp(order, 16, 256)` and `m = clamp(order, 1, 48)`. A pure
/// function of `order` — the memo table changes what it costs, never what it
/// returns. Returns `None` only when a kernel runs out of reduction budget.
///
/// ```
/// use axeyum_cas::enclosure_integral::euler_gamma;
/// // gamma = 0.5772156649015328606065120900824...
/// let g = euler_gamma(64).unwrap();
/// assert!(g.decimal(9).starts_with("[0.577215664"));
/// ```
#[must_use]
pub fn euler_gamma(order: u32) -> Option<BigInterval> {
    if let Ok(map) = gamma_cache().lock()
        && let Some(cached) = map.get(&order)
    {
        return Some(cached.clone());
    }
    let value = euler_gamma_uncached(order)?;
    if let Ok(mut map) = gamma_cache().lock() {
        map.insert(order, value.clone());
    }
    Some(value)
}

/// [`euler_gamma`] without the memo table — the definition itself.
fn euler_gamma_uncached(order: u32) -> Option<BigInterval> {
    let n = order.clamp(16, EULER_ANCHOR_CAP);
    let terms = order.clamp(1, EULER_TERMS_CAP);
    let anchor = bi_u64(u64::from(n));
    let mut harmonic = BigRational::zero();
    for k in 1..n {
        harmonic += BigRational::new(BigInt::one(), BigInt::from(k));
    }
    // The `ln n` series is cheap here (every anchor on the order ladder is a
    // power of two, so the `atanh` argument is exactly 0 and only `ln 2` runs),
    // so it is taken at twice the order to keep it off the critical path.
    let logarithm = ln_point(&anchor, order.saturating_mul(2).max(24))?;
    let bernoulli = bernoulli_table(2 * terms);
    let mut total = BigInterval::point(harmonic)
        .sub(&logarithm)
        .add(&BigInterval::point(BigRational::one() / (bi(2) * &anchor)));
    for j in 1..=terms {
        let index = 2 * usize::try_from(j).ok()?;
        let term = &bernoulli[index] / (bi_u64(index as u64) * ratpow_big(&anchor, 2 * j));
        total = total.add(&BigInterval::point(term));
    }
    let last = 2 * usize::try_from(terms).ok()?;
    let error = (&bernoulli[last] / (bi_u64(last as u64) * ratpow_big(&anchor, 2 * terms))).abs();
    BigInterval::new(total.lo() - &error, total.hi() + &error)
}

/// `x^n` for a `BigRational` base — the parent module's `ratpow`, re-exported
/// under a local name so this module has one import fewer to keep in step.
fn ratpow_big(x: &BigRational, n: u32) -> BigRational {
    let mut result = BigRational::one();
    let mut base = x.clone();
    let mut exponent = n;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result *= &base;
        }
        base = &base * &base;
        exponent >>= 1;
    }
    result
}

// ---------------------------------------------------------------------------
// Si and Shi.
// ---------------------------------------------------------------------------

/// The dyadic grid a **tail-bound magnitude** is rounded up onto.
///
/// Every tail bound and every monotonicity index below is monotone increasing
/// in the argument's magnitude, so replacing that magnitude by anything at or
/// above it keeps the bound valid and the index conservative. Rounding it onto
/// a coarse grid is what stops `a^(2n+3)` from being a half-million-bit
/// rational: a magnitude taken from a certified `π` at order 128 has
/// two-thousand-bit endpoints, and the Fresnel tail raises `π/2` to the 258th
/// power. Measured 2026-09-05 in a debug build, the two Fresnel heads at
/// precision 130 took **48.5 s** before this rounding.
const MAGNITUDE_BITS: u32 = 32;

/// The largest absolute value the interval reaches, rounded **up** onto the
/// [`MAGNITUDE_BITS`] grid.
///
/// Never below the true magnitude, which is the only property every consumer
/// below needs.
fn magnitude(x: &BigInterval) -> BigRational {
    dyadic_ceil(&rmax(x.lo().abs(), x.hi().abs()), MAGNITUDE_BITS)
}

/// Reject an argument past [`SERIES_MAGNITUDE_LIMIT`].
fn within_series_range(a: &BigRational) -> Result<(), DeclineReason> {
    if *a > bi(SERIES_MAGNITUDE_LIMIT) {
        return Err(DeclineReason::ResourceLimit);
    }
    Ok(())
}

/// The least `k` from which the `Si`/`Shi` terms
/// `a^(2k+1)/((2k+1)·(2k+1)!)` are non-increasing: the exact condition is
/// `a²(2k+1) <= (2k+2)(2k+3)²`, whose right side is cubic in `k` and left side
/// linear, so once it holds it holds for every larger `k`.
fn odd_series_index(a: &BigRational) -> Option<u32> {
    let a2 = a * a;
    for k in 0..INDEX_CAP {
        let k64 = u64::from(k);
        let left = &a2 * bi_u64(2 * k64 + 1);
        let right = bi_u64(2 * k64 + 2) * bi_u64(2 * k64 + 3) * bi_u64(2 * k64 + 3);
        if left <= right {
            return Some(k);
        }
    }
    None
}

/// The exact ratio `t_(k+1)/t_k = a²(2k+1)/((2k+2)(2k+3)²)` of the `Si`/`Shi`
/// terms at index `k`. Decreasing in `k`, so the value at the first omitted
/// index dominates the whole tail.
fn odd_series_ratio(a: &BigRational, k: u32) -> BigRational {
    let k64 = u64::from(k);
    (a * a) * bi_u64(2 * k64 + 1)
        / (bi_u64(2 * k64 + 2) * bi_u64(2 * k64 + 3) * bi_u64(2 * k64 + 3))
}

/// The partial sum `Σ_(k=0)^order sign^k x^(2k+1)/((2k+1)·(2k+1)!)` over an
/// interval, and the magnitude of the first omitted term at `a`.
///
/// Shared by `Si` (`alternating = true`) and `Shi` (`false`); the sum differs
/// only in the sign, and the tail bound is the caller's business.
fn odd_partial_sum(
    x: &BigInterval,
    a: &BigRational,
    order: u32,
    alternating: bool,
) -> (BigInterval, BigRational) {
    let square = round_series(&x.pow(2), order);
    let mut power = round_series(x, order);
    let mut factorial = BigRational::one();
    let mut sum = x.clone();
    let mut sign = if alternating { -1i64 } else { 1i64 };
    for k in 1..=order {
        let k64 = u64::from(k);
        power = round_series(&power.mul(&square), order);
        factorial *= bi_u64(2 * k64) * bi_u64(2 * k64 + 1);
        let coefficient = bi(sign) / (bi_u64(2 * k64 + 1) * &factorial);
        sum = round_series(&sum.add(&power.scale(&coefficient)), order);
        if alternating {
            sign = -sign;
        }
    }
    let next = u64::from(order) + 1;
    let next_factorial = &factorial * bi_u64(2 * next) * bi_u64(2 * next + 1);
    let omitted = ratpow_big(a, 2 * order + 3) / (bi_u64(2 * next + 1) * next_factorial);
    (sum, omitted)
}

/// The **sine integral** `Si(x) = ∫₀ˣ sin t / t dt` over an interval.
///
/// Alternating Maclaurin series; the bound is the first omitted term, valid
/// because `order` is at or above [`odd_series_index`], which is the exact
/// index from which the terms fall.
///
/// # Errors
///
/// [`DeclineReason::ResourceLimit`] past [`SERIES_MAGNITUDE_LIMIT`],
/// [`DeclineReason::PrecisionUnreachable`] below the monotonicity index.
pub(crate) fn si_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    let a = magnitude(x);
    within_series_range(&a)?;
    let start = odd_series_index(&a).ok_or(DeclineReason::ResourceLimit)?;
    if order < start {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let (sum, omitted) = odd_partial_sum(x, &a, order, true);
    BigInterval::new(sum.lo() - &omitted, sum.hi() + &omitted)
        .ok_or(DeclineReason::PrecisionUnreachable)
}

/// The **hyperbolic sine integral** `Shi(x) = ∫₀ˣ sinh t / t dt` over an
/// interval.
///
/// Same series without the alternating sign, so the tail needs a geometric
/// majorant: with `R` the exact term ratio at the first omitted index (and the
/// ratio decreasing in `k`), the tail is at most `t_(n+1)/(1 − R)`. The module
/// declines while `R >= 1/2` so the majorant is never marginal.
///
/// # Errors
///
/// As [`si_interval`]; also [`DeclineReason::PrecisionUnreachable`] while the
/// ratio at the first omitted index is at least `1/2`.
pub(crate) fn shi_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    let a = magnitude(x);
    within_series_range(&a)?;
    let ratio = odd_series_ratio(&a, order + 1);
    if ratio >= br(1, 2) {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let (sum, omitted) = odd_partial_sum(x, &a, order, false);
    let tail = omitted / (BigRational::one() - ratio);
    BigInterval::new(sum.lo() - &tail, sum.hi() + &tail).ok_or(DeclineReason::PrecisionUnreachable)
}

// ---------------------------------------------------------------------------
// Ci and Chi.
// ---------------------------------------------------------------------------

/// The least `k >= 1` from which the `Ci`/`Chi` terms
/// `a^(2k)/(2k·(2k)!)` are non-increasing: `2k·a² <= (2k+1)(2k+2)²`.
fn even_series_index(a: &BigRational) -> Option<u32> {
    let a2 = a * a;
    for k in 1..INDEX_CAP {
        let k64 = u64::from(k);
        let left = &a2 * bi_u64(2 * k64);
        let right = bi_u64(2 * k64 + 1) * bi_u64(2 * k64 + 2) * bi_u64(2 * k64 + 2);
        if left <= right {
            return Some(k);
        }
    }
    None
}

/// The exact ratio `t_(k+1)/t_k = 2k·a²/((2k+1)(2k+2)²)` of the `Ci`/`Chi`
/// terms at index `k`, decreasing in `k`.
fn even_series_ratio(a: &BigRational, k: u32) -> BigRational {
    let k64 = u64::from(k);
    (a * a) * bi_u64(2 * k64) / (bi_u64(2 * k64 + 1) * bi_u64(2 * k64 + 2) * bi_u64(2 * k64 + 2))
}

/// The partial sum `Σ_(k=1)^order sign^k x^(2k)/(2k·(2k)!)` over an interval,
/// and the magnitude of the first omitted term at `a`.
fn even_partial_sum(
    x: &BigInterval,
    a: &BigRational,
    order: u32,
    alternating: bool,
) -> (BigInterval, BigRational) {
    let square = round_series(&x.pow(2), order);
    let mut power = BigInterval::point(BigRational::one());
    let mut factorial = BigRational::one();
    let mut sum = BigInterval::point(BigRational::zero());
    let mut sign = 1i64;
    for k in 1..=order.max(1) {
        let k64 = u64::from(k);
        power = round_series(&power.mul(&square), order);
        factorial *= bi_u64(2 * k64 - 1) * bi_u64(2 * k64);
        if alternating {
            sign = -sign;
        }
        let coefficient = bi(sign) / (bi_u64(2 * k64) * &factorial);
        sum = round_series(&sum.add(&power.scale(&coefficient)), order);
    }
    let count = order.max(1);
    let next = u64::from(count) + 1;
    let next_factorial = &factorial * bi_u64(2 * next - 1) * bi_u64(2 * next);
    let omitted = ratpow_big(a, 2 * count + 2) / (bi_u64(2 * next) * next_factorial);
    (sum, omitted)
}

/// `γ + ln x` over a strictly positive interval — the non-series half of `Ci`,
/// `Chi` and `Ei`.
///
/// The logarithm goes through [`ln_large`], **not** the parent module's
/// `ln_point`, because the argument here is a *computed* interval: `li x` is
/// `Ei(ln x)`, so `Ei` receives an endpoint that already carries a certified
/// logarithm's denominator, and `ln_point` forms `z^(2·order+1)` of it.
/// Measured 2026-09-05 in a debug build, `li(2)` at precision 130 took
/// **104.7 s** through `ln_point` — a 58,000-bit intermediate — and about a
/// second through `ln_large`, which anchors on a 16-bit dyadic instead.
fn log_and_gamma(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    let low = ln_large(x.lo(), order).ok_or(DeclineReason::ResourceLimit)?;
    let high = ln_large(x.hi(), order).ok_or(DeclineReason::ResourceLimit)?;
    let logarithm = BigInterval::new(low.lo().clone(), high.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    let gamma = euler_gamma(order).ok_or(DeclineReason::ResourceLimit)?;
    Ok(logarithm.add(&gamma))
}

/// The **cosine integral** `Ci(x) = γ + ln x + ∫₀ˣ (cos t − 1)/t dt` over a
/// strictly positive interval.
///
/// # Errors
///
/// [`DeclineReason::DomainError`] for an argument reaching `0` or below, and
/// the declines of [`si_interval`] and [`euler_gamma`].
pub(crate) fn ci_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    if !x.lo().is_positive() {
        return Err(DeclineReason::DomainError(
            "Ci of an interval reaching 0 or below".to_string(),
        ));
    }
    let a = magnitude(x);
    within_series_range(&a)?;
    let start = even_series_index(&a).ok_or(DeclineReason::ResourceLimit)?;
    if order < start {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let (sum, omitted) = even_partial_sum(x, &a, order, true);
    let series = BigInterval::new(sum.lo() - &omitted, sum.hi() + &omitted)
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    Ok(log_and_gamma(x, order)?.add(&series))
}

/// The **hyperbolic cosine integral** `Chi(x) = γ + ln x + ∫₀ˣ (cosh t − 1)/t dt`
/// over a strictly positive interval, with the geometric majorant of
/// [`shi_interval`].
///
/// # Errors
///
/// As [`ci_interval`], plus [`DeclineReason::PrecisionUnreachable`] while the
/// term ratio at the first omitted index is at least `1/2`.
pub(crate) fn chi_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    if !x.lo().is_positive() {
        return Err(DeclineReason::DomainError(
            "Chi of an interval reaching 0 or below".to_string(),
        ));
    }
    let a = magnitude(x);
    within_series_range(&a)?;
    let ratio = even_series_ratio(&a, order.max(1) + 1);
    if ratio >= br(1, 2) {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let (sum, omitted) = even_partial_sum(x, &a, order, false);
    let tail = omitted / (BigRational::one() - ratio);
    let series = BigInterval::new(sum.lo() - &tail, sum.hi() + &tail)
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    Ok(log_and_gamma(x, order)?.add(&series))
}

// ---------------------------------------------------------------------------
// Ei and li.
// ---------------------------------------------------------------------------

/// The **exponential integral** `Ei(x) = γ + ln abs(x) + Σ_(k>=1) x^k/(k·k!)`
/// over an interval that does not contain `0`.
///
/// The terms satisfy `abs(t_(k+1)/t_k) = a·k/(k+1)² <= a/(k+1)`, so with
/// `R = a/(order+2)` the tail is at most `t_(order+1)/(1 − R)` — a geometric
/// majorant that holds for a **negative** argument too, where the series
/// alternates and the bound is merely generous.
///
/// # Errors
///
/// [`DeclineReason::DomainError`] when the argument contains `0` (`Ei` has a
/// logarithmic singularity there), [`DeclineReason::ResourceLimit`] past
/// [`SERIES_MAGNITUDE_LIMIT`], [`DeclineReason::PrecisionUnreachable`] while
/// `R >= 1/2`.
pub(crate) fn ei_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    if x.contains(&BigRational::zero()) {
        return Err(DeclineReason::DomainError(
            "Ei of an interval containing 0".to_string(),
        ));
    }
    let a = magnitude(x);
    within_series_range(&a)?;
    let count = order.max(1);
    let ratio = &a / bi_u64(u64::from(count) + 2);
    if ratio >= br(1, 2) {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let rounded = round_series(x, order);
    let mut power = BigInterval::point(BigRational::one());
    let mut factorial = BigRational::one();
    let mut sum = BigInterval::point(BigRational::zero());
    for k in 1..=count {
        let k64 = u64::from(k);
        power = round_series(&power.mul(&rounded), order);
        factorial *= bi_u64(k64);
        let coefficient = BigRational::one() / (bi_u64(k64) * &factorial);
        sum = round_series(&sum.add(&power.scale(&coefficient)), order);
    }
    let next = u64::from(count) + 1;
    let next_factorial = &factorial * bi_u64(next);
    let omitted = ratpow_big(&a, count + 1) / (bi_u64(next) * next_factorial);
    let tail = omitted / (BigRational::one() - ratio);
    let series = BigInterval::new(sum.lo() - &tail, sum.hi() + &tail)
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    // ln abs(x): the argument does not straddle 0, so the absolute value of
    // the interval is again an interval, and `ln` is increasing on it.
    let absolute = if x.hi().is_negative() {
        x.negate()
    } else {
        x.clone()
    };
    Ok(log_and_gamma(&absolute, order)?.add(&series))
}

/// The **logarithmic integral** `li(x) = Ei(ln x)` over an interval that is
/// strictly positive and does not contain `1`.
///
/// The composition is exact — `li` and `Ei` are the same function of `ln x` —
/// so the evidence is the `ln` bound followed by the `Ei` bound, with no third
/// series and no new hypothesis. `li` is the Cauchy principal value through
/// the singularity at `1`, which is why an argument containing `1` declines.
///
/// # Errors
///
/// [`DeclineReason::DomainError`] for an argument reaching `0` or below or
/// containing `1`; otherwise the declines of [`ei_interval`].
pub(crate) fn li_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    if !x.lo().is_positive() {
        return Err(DeclineReason::DomainError(
            "li of an interval reaching 0 or below".to_string(),
        ));
    }
    if x.contains(&BigRational::one()) {
        return Err(DeclineReason::DomainError(
            "li of an interval containing 1".to_string(),
        ));
    }
    let low = ln_large(x.lo(), order).ok_or(DeclineReason::ResourceLimit)?;
    let high = ln_large(x.hi(), order).ok_or(DeclineReason::ResourceLimit)?;
    let logarithm = BigInterval::new(low.lo().clone(), high.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    // The `ln` enclosure is wider than a point, so it can straddle 0 even when
    // the argument does not contain 1; that is a genuine precision decline.
    ei_interval(&coarsen(&logarithm, grid_bits(order)), order)
}

// ---------------------------------------------------------------------------
// The Fresnel integrals.
// ---------------------------------------------------------------------------

/// `π/2` as an interval, and its upper endpoint as a bound on the series
/// coefficient growth.
fn half_pi(order: u32) -> Result<(BigInterval, BigRational), DeclineReason> {
    let pi = pi_enclosure(order).ok_or(DeclineReason::ResourceLimit)?;
    let half = pi.scale(&br(1, 2));
    // Rounded UP onto the coarse grid for the same reason `magnitude` is: this
    // value is raised to the `2n+2`-th power in the tail bound, and only its
    // being an upper bound on `π/2` matters there.
    let bound = dyadic_ceil(half.hi(), MAGNITUDE_BITS);
    Ok((half, bound))
}

/// The least `k` from which the Fresnel `C` terms are non-increasing, at the
/// **upper** bounds `p >= π/2` and `a >= abs(x)`: the ratio
/// `p²a⁴(4k+1)/((2k+1)(2k+2)(4k+5))` grows with both, so bounding both above
/// is sufficient for the true ratio.
fn fresnel_c_index(p: &BigRational, a: &BigRational) -> Option<u32> {
    let scale = (p * p) * ratpow_big(a, 4);
    for k in 0..INDEX_CAP {
        let k64 = u64::from(k);
        let left = &scale * bi_u64(4 * k64 + 1);
        let right = bi_u64(2 * k64 + 1) * bi_u64(2 * k64 + 2) * bi_u64(4 * k64 + 5);
        if left <= right {
            return Some(k);
        }
    }
    None
}

/// The least `k` from which the Fresnel `S` terms are non-increasing, by the
/// same argument with the ratio `p²a⁴(4k+3)/((2k+2)(2k+3)(4k+7))`.
fn fresnel_s_index(p: &BigRational, a: &BigRational) -> Option<u32> {
    let scale = (p * p) * ratpow_big(a, 4);
    for k in 0..INDEX_CAP {
        let k64 = u64::from(k);
        let left = &scale * bi_u64(4 * k64 + 3);
        let right = bi_u64(2 * k64 + 2) * bi_u64(2 * k64 + 3) * bi_u64(4 * k64 + 7);
        if left <= right {
            return Some(k);
        }
    }
    None
}

/// The **Fresnel cosine integral** `C(x) = ∫₀ˣ cos(π t²/2) dt` over an
/// interval, by `Σ (−1)^k (π/2)^(2k) x^(4k+1)/((2k)!(4k+1))`.
///
/// # Errors
///
/// [`DeclineReason::ResourceLimit`] past [`SERIES_MAGNITUDE_LIMIT`],
/// [`DeclineReason::PrecisionUnreachable`] below the monotonicity index.
pub(crate) fn fresnel_c_interval(
    x: &BigInterval,
    order: u32,
) -> Result<BigInterval, DeclineReason> {
    let a = magnitude(x);
    within_series_range(&a)?;
    let (half, bound) = half_pi(order)?;
    let start = fresnel_c_index(&bound, &a).ok_or(DeclineReason::ResourceLimit)?;
    if order < start {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let half_square = round_series(&half.pow(2), order);
    let fourth = round_series(&x.pow(4), order);
    let mut coefficient = BigInterval::point(BigRational::one());
    let mut power = round_series(x, order);
    let mut factorial = BigRational::one();
    let mut sum = x.clone();
    let mut sign = -1i64;
    for k in 1..=order {
        let k64 = u64::from(k);
        coefficient = round_series(&coefficient.mul(&half_square), order);
        power = round_series(&power.mul(&fourth), order);
        factorial *= bi_u64(2 * k64 - 1) * bi_u64(2 * k64);
        let scale = bi(sign) / (&factorial * bi_u64(4 * k64 + 1));
        sum = round_series(&sum.add(&coefficient.mul(&power).scale(&scale)), order);
        sign = -sign;
    }
    let next = u64::from(order) + 1;
    let next_factorial = &factorial * bi_u64(2 * next - 1) * bi_u64(2 * next);
    let omitted = ratpow_big(&bound, 2 * order + 2) * ratpow_big(&a, 4 * order + 5)
        / (next_factorial * bi_u64(4 * next + 1));
    BigInterval::new(sum.lo() - &omitted, sum.hi() + &omitted)
        .ok_or(DeclineReason::PrecisionUnreachable)
}

/// The **Fresnel sine integral** `S(x) = ∫₀ˣ sin(π t²/2) dt` over an interval,
/// by `Σ (−1)^k (π/2)^(2k+1) x^(4k+3)/((2k+1)!(4k+3))`.
///
/// # Errors
///
/// As [`fresnel_c_interval`].
pub(crate) fn fresnel_s_interval(
    x: &BigInterval,
    order: u32,
) -> Result<BigInterval, DeclineReason> {
    let a = magnitude(x);
    within_series_range(&a)?;
    let (half, bound) = half_pi(order)?;
    let start = fresnel_s_index(&bound, &a).ok_or(DeclineReason::ResourceLimit)?;
    if order < start {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let half_square = round_series(&half.pow(2), order);
    let fourth = round_series(&x.pow(4), order);
    let mut coefficient = round_series(&half, order);
    let mut power = round_series(&x.pow(3), order);
    let mut factorial = BigRational::one();
    let mut sum = coefficient.mul(&power).scale(&br(1, 3));
    let mut sign = -1i64;
    for k in 1..=order {
        let k64 = u64::from(k);
        coefficient = round_series(&coefficient.mul(&half_square), order);
        power = round_series(&power.mul(&fourth), order);
        factorial *= bi_u64(2 * k64) * bi_u64(2 * k64 + 1);
        let scale = bi(sign) / (&factorial * bi_u64(4 * k64 + 3));
        sum = round_series(&sum.add(&coefficient.mul(&power).scale(&scale)), order);
        sign = -sign;
    }
    let next = u64::from(order) + 1;
    let next_factorial = &factorial * bi_u64(2 * next) * bi_u64(2 * next + 1);
    let omitted = ratpow_big(&bound, 2 * order + 3) * ratpow_big(&a, 4 * order + 7)
        / (next_factorial * bi_u64(4 * next + 3));
    BigInterval::new(sum.lo() - &omitted, sum.hi() + &omitted)
        .ok_or(DeclineReason::PrecisionUnreachable)
}

// ---------------------------------------------------------------------------
// asin, acos, asinh, acosh.
// ---------------------------------------------------------------------------

/// `asin(z)` for a rational `abs(z) <= 3/4`, by
/// `Σ_(k>=0) C(2k,k) z^(2k+1)/(4^k(2k+1))`.
///
/// The ratio `t_(k+1)/t_k = z²(2k+1)²/((2k+2)(2k+3))` is strictly below `z²`
/// for every `k`, so the tail past term `n` is at most
/// `t_(n+1)/(1 − z²)` — a geometric majorant needing only `abs(z) < 1`, with no
/// monotonicity index to compute.
fn asin_series(z: &BigRational, order: u32) -> Option<BigInterval> {
    if z.abs() > br(3, 4) {
        return None;
    }
    let square = z * z;
    let mut power = z.clone();
    let mut coefficient = BigRational::one();
    let mut sum = z.clone();
    for k in 1..=order {
        let k64 = u64::from(k);
        // C(2k,k)/4^k from C(2k−2,k−1)/4^(k−1) by the ratio (2k−1)/(2k).
        coefficient *= bi_u64(2 * k64 - 1) / bi_u64(2 * k64);
        power *= &square;
        sum += &coefficient * &power / bi_u64(2 * k64 + 1);
    }
    let next = u64::from(order) + 1;
    let next_coefficient = &coefficient * bi_u64(2 * next - 1) / bi_u64(2 * next);
    let omitted = (next_coefficient * &power * &square / bi_u64(2 * next + 1)).abs();
    let denominator = BigRational::one() - &square;
    if !denominator.is_positive() {
        return None;
    }
    let tail = omitted / denominator;
    Some(BigInterval::center_radius(&sum, &tail))
}

/// `asin(p)` for a rational `abs(p) <= 1`.
///
/// `abs(p) <= 1/2` takes the series directly. Beyond that the exact half-angle
/// identity `asin p = π/2 − 2·asin √((1−p)/2)` reduces the argument to at most
/// `1/2` (for `p` in `[1/2, 1]` the inner argument lies in `[0, 1/2]`), so the
/// slow region near `±1` is never entered. One level of recursion.
fn asin_point(p: &BigRational, order: u32) -> Option<BigInterval> {
    let one = BigRational::one();
    let a = p.abs();
    if a > one {
        return None;
    }
    let positive = if a <= br(1, 2) {
        asin_series(&a, order)?
    } else {
        let inner = (&one - &a) / bi(2);
        let root = round_series(&nth_root_point(&inner, 2, order)?, order);
        let low = asin_series(root.lo(), order)?;
        let high = asin_series(root.hi(), order)?;
        let reduced = BigInterval::new(low.lo().clone(), high.hi().clone())?;
        let pi = pi_enclosure(order)?;
        pi.scale(&br(1, 2)).sub(&reduced.scale(&bi(2)))
    };
    Some(if p.is_negative() {
        positive.negate()
    } else {
        positive
    })
}

/// **Arcsine** over an interval inside `[−1, 1]`. `asin` is increasing, so the
/// image is bracketed by the two endpoint evaluations.
///
/// # Errors
///
/// [`DeclineReason::DomainError`] when the argument leaves `[−1, 1]`.
pub(crate) fn asin_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    let one = BigRational::one();
    if x.lo() < &-one.clone() || x.hi() > &one {
        return Err(DeclineReason::DomainError(
            "asin of an interval leaving [-1, 1]".to_string(),
        ));
    }
    let low = asin_point(x.lo(), order).ok_or(DeclineReason::PrecisionUnreachable)?;
    let high = asin_point(x.hi(), order).ok_or(DeclineReason::PrecisionUnreachable)?;
    BigInterval::new(low.lo().clone(), high.hi().clone()).ok_or(DeclineReason::PrecisionUnreachable)
}

/// **Arccosine** over an interval inside `[−1, 1]`, as `π/2 − asin x`.
///
/// # Errors
///
/// As [`asin_interval`].
pub(crate) fn acos_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    let sine = asin_interval(x, order)?;
    let pi = pi_enclosure(order).ok_or(DeclineReason::ResourceLimit)?;
    Ok(pi.scale(&br(1, 2)).sub(&sine))
}

/// `asinh(p) = sign(p)·ln(abs(p) + √(p²+1))` for a rational `p`.
///
/// The identity is exact on all of `ℝ` and needs no series of its own — only
/// the certified `√` and `ln` the parent modules already carry. Taking the
/// absolute value first is what keeps it accurate: for a large negative `p`,
/// `p + √(p²+1)` is a difference of nearly equal quantities, and while exact
/// rational arithmetic loses nothing, the `√` **bracket** would be wide
/// relative to the value.
fn asinh_point(p: &BigRational, order: u32) -> Option<BigInterval> {
    let a = p.abs();
    let radicand = &a * &a + BigRational::one();
    let root = nth_root_point(&radicand, 2, order)?;
    // Rounded outward before it reaches `ln`: the Newton bracket's lower
    // endpoint is `p/x^(q−1)`, which carries twice the iterate's denominator,
    // and everything downstream only needs an enclosure.
    let argument = round_series(&root.add(&BigInterval::point(a)), order);
    let low = ln_large(argument.lo(), order)?;
    let high = ln_large(argument.hi(), order)?;
    let positive = BigInterval::new(low.lo().clone(), high.hi().clone())?;
    Some(if p.is_negative() {
        positive.negate()
    } else {
        positive
    })
}

/// **Inverse hyperbolic sine** over an interval. Increasing everywhere, so the
/// two endpoints bracket the image; the domain is all of `ℝ`.
///
/// # Errors
///
/// [`DeclineReason::PrecisionUnreachable`] when a kernel declines.
pub(crate) fn asinh_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    let low = asinh_point(x.lo(), order).ok_or(DeclineReason::PrecisionUnreachable)?;
    let high = asinh_point(x.hi(), order).ok_or(DeclineReason::PrecisionUnreachable)?;
    BigInterval::new(low.lo().clone(), high.hi().clone()).ok_or(DeclineReason::PrecisionUnreachable)
}

/// `acosh(p) = ln(p + √(p²−1))` for a rational `p >= 1`.
fn acosh_point(p: &BigRational, order: u32) -> Option<BigInterval> {
    if *p < BigRational::one() {
        return None;
    }
    let radicand = p * p - BigRational::one();
    let root = nth_root_point(&radicand, 2, order)?;
    let argument = round_series(&root.add(&BigInterval::point(p.clone())), order);
    let low = ln_large(argument.lo(), order)?;
    let high = ln_large(argument.hi(), order)?;
    BigInterval::new(low.lo().clone(), high.hi().clone())
}

/// **Inverse hyperbolic cosine** over an interval inside `[1, ∞)`. Increasing,
/// so the endpoints bracket the image.
///
/// # Errors
///
/// [`DeclineReason::DomainError`] when the argument reaches below `1`.
pub(crate) fn acosh_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    if *x.lo() < BigRational::one() {
        return Err(DeclineReason::DomainError(
            "acosh of an interval reaching below 1".to_string(),
        ));
    }
    let low = acosh_point(x.lo(), order).ok_or(DeclineReason::PrecisionUnreachable)?;
    let high = acosh_point(x.hi(), order).ok_or(DeclineReason::PrecisionUnreachable)?;
    BigInterval::new(low.lo().clone(), high.hi().clone()).ok_or(DeclineReason::PrecisionUnreachable)
}

// ---------------------------------------------------------------------------
// Symbolic exponents and atanh.
// ---------------------------------------------------------------------------

/// The expression `base^exponent` for an **arbitrary** exponent expression,
/// built as `exp(exponent · ln base)`.
///
/// No new head: the evidence is the certified `Ln`, `Mul` and `Exp` the parent
/// module already has, and [`crate::enclosure::Enclosure::verify`] checks it
/// unchanged. Valid only where `base` encloses to a **strictly positive**
/// interval — see [`enclose_symbolic_power`], which says so with a reason
/// naming `pow`.
///
/// ```
/// use axeyum_cas::CasExpr;
/// use axeyum_cas::enclosure::enclose;
/// use axeyum_cas::enclosure_integral::symbolic_power;
/// // 2^(1/2) = 1.41421356...
/// let expr = symbolic_power(CasExpr::int(2), CasExpr::rat(1, 2));
/// let e = enclose(&expr, &[], 60).unwrap();
/// assert!(e.interval.decimal(6).starts_with("[1.414213"));
/// ```
#[must_use]
pub fn symbolic_power(base: CasExpr, exponent: CasExpr) -> CasExpr {
    CasExpr::Unary(
        UnaryFunc::Exp,
        Box::new(CasExpr::Mul(vec![
            exponent,
            CasExpr::Unary(UnaryFunc::Ln, Box::new(base)),
        ])),
    )
}

/// `atanh(x) = (1/2)·ln((1+x)/(1−x))` as an expression.
///
/// [`UnaryFunc`] has no `Atanh` variant, so `atanh` is a **constructor** here
/// rather than a head: the certificate names `Ln`, `Div`, `Add` and `Mul`, and
/// the identity is exact on `(−1, 1)`. An argument reaching `±1` declines
/// through the `ln` domain error or the zero divisor, as it should.
///
/// ```
/// use axeyum_cas::CasExpr;
/// use axeyum_cas::enclosure::enclose;
/// use axeyum_cas::enclosure_integral::atanh_expr;
/// // atanh(1/2) = 0.5493061443340548...
/// let e = enclose(&atanh_expr(CasExpr::rat(1, 2)), &[], 60).unwrap();
/// assert!(e.interval.decimal(6).starts_with("[0.549306"));
/// ```
#[must_use]
pub fn atanh_expr(x: CasExpr) -> CasExpr {
    let numerator = CasExpr::Add(vec![CasExpr::int(1), x.clone()]);
    let denominator = CasExpr::Add(vec![CasExpr::int(1), CasExpr::Neg(Box::new(x))]);
    CasExpr::Mul(vec![
        CasExpr::rat(1, 2),
        CasExpr::Unary(
            UnaryFunc::Ln,
            Box::new(CasExpr::Div(Box::new(numerator), Box::new(denominator))),
        ),
    ])
}

/// A certified enclosure of `base^exponent` over a binding box, through
/// [`symbolic_power`].
///
/// The base is enclosed first, so a base reaching `0` or below declines with
/// [`DeclineReason::DomainError`] naming `pow` — a different message from the
/// `ln` domain error the raw composition produces, which is what lets a caller
/// tell "this exponentiation is outside the real branch" from "some logarithm
/// somewhere left its domain".
///
/// # Errors
///
/// [`DeclineReason::DomainError`] for a base reaching `0` or below; otherwise
/// the declines of [`crate::enclosure::enclose_with_reason`].
pub fn enclose_symbolic_power(
    base: &CasExpr,
    exponent: &CasExpr,
    bindings: &[(&str, Interval)],
    precision: u32,
) -> Result<crate::enclosure::Enclosure, DeclineReason> {
    let mut map = BTreeMap::new();
    for (name, interval) in bindings {
        map.insert((*name).to_string(), BigInterval::from_interval(interval));
    }
    // `enclose_fixed_order`, not `enclose`: the probe asks only whether the base
    // is positive, and a base bound to a WIDE box (`x` in `[-1, 1]`) can never
    // meet a width guard, so going through `enclose` would report
    // `PrecisionUnreachable` for what is really a domain question.
    let probe = enclose_fixed_order(base, &map, BASE_PROBE_ORDER)?;
    if !probe.lo().is_positive() {
        return Err(DeclineReason::DomainError(
            "pow: the base interval reaches 0 or below, so x^y has no real branch".to_string(),
        ));
    }
    let expr = symbolic_power(base.clone(), exponent.clone());
    enclose_with_reason(&expr, bindings, precision)
}

// ---------------------------------------------------------------------------
// Definite integrals.
// ---------------------------------------------------------------------------

/// Which quadrature rule an [`IntegralEnclosure`] used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuadratureRule {
    /// Simpson's rule with the fourth-derivative error term
    /// `−(w^5/2880)·f⁗(ξ)`; converges like `w^4` and needs `f⁗` enclosable
    /// over each panel.
    Simpson,
    /// `∫ ⊆ w · F([u, v])`; converges linearly, needs nothing but an
    /// enclosure of `f`, and is always sound.
    Box,
}

/// One panel of an [`IntegralEnclosure`]'s partition, with the evaluations
/// that produced its contribution.
///
/// The verifier recomputes every field from `(f, var, lo, hi, order, rule)` and
/// never reads one as an answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegralPanel {
    /// The panel's lower endpoint. Dyadic except for the first panel, whose
    /// endpoint is the core lower limit.
    pub lo: BigRational,
    /// The panel's upper endpoint.
    pub hi: BigRational,
    /// `f` at `lo` (Simpson) or over `[lo, hi]` (box rule).
    pub at_lo: BigInterval,
    /// `f` at the midpoint. Simpson only; the point interval `0` for the box
    /// rule.
    pub at_mid: BigInterval,
    /// `f` at `hi`. Simpson only.
    pub at_hi: BigInterval,
    /// An enclosure of `f⁗` over the panel. Simpson only.
    pub fourth: BigInterval,
    /// The panel's claimed enclosure of `∫_lo^hi f`.
    pub value: BigInterval,
}

/// A rational interval enclosing `∫_a^b f`, with the quadrature evidence that
/// produced it.
///
/// Produced by [`enclose_integral`], checked by [`IntegralEnclosure::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegralEnclosure {
    /// The interval. Contains `∫_a^b f` for **every** `a` in `lower` and every
    /// `b` in `upper`, with width at most `2^(−precision)`.
    pub interval: BigInterval,
    /// The requested precision.
    pub precision: u32,
    /// The rule used on every panel.
    pub rule: QuadratureRule,
    /// The fixed truncation order every integrand evaluation used, so the
    /// verifier reproduces them exactly.
    pub order: u32,
    /// The lower limit of integration, as supplied.
    pub lower: BigInterval,
    /// The upper limit of integration, as supplied.
    pub upper: BigInterval,
    /// The partition of the dyadic core, in increasing order.
    pub panels: Vec<IntegralPanel>,
    /// The box the lower sliver `[lower.lo, panels[0].lo]` was bounded over.
    pub low_edge_box: BigInterval,
    /// The box the upper sliver `[panels.last().hi, upper.hi]` was bounded
    /// over.
    pub high_edge_box: BigInterval,
    /// The claimed enclosure of `∫` over the lower sliver.
    pub low_edge: BigInterval,
    /// The claimed enclosure of `∫` over the upper sliver.
    pub high_edge: BigInterval,
}

/// The fixed evaluation order a request at `precision` uses.
///
/// Deterministic in the precision alone and recorded in the certificate, so a
/// later change to this ladder cannot invalidate an existing certificate.
fn quadrature_order(precision: u32) -> u32 {
    match precision {
        0..=20 => 16,
        21..=40 => 32,
        41..=100 => 64,
        _ => 128,
    }
}

/// The dyadic grid the partition and the edge boxes are placed on.
fn quadrature_bits(precision: u32) -> u32 {
    precision.saturating_add(32)
}

/// The magnitude bound `max(abs(lo), abs(hi))` of an interval.
fn sup_abs(x: &BigInterval) -> BigRational {
    rmax(x.lo().abs(), x.hi().abs())
}

/// Enclose `f` over a box, at the fixed order, reporting the panel when it
/// fails.
fn integrand_over(
    f: &CasExpr,
    var: &str,
    box_: &BigInterval,
    order: u32,
) -> Result<BigInterval, DeclineReason> {
    let mut bindings = BTreeMap::new();
    bindings.insert(var.to_string(), box_.clone());
    enclose_fixed_order(f, &bindings, order).map_err(|reason| {
        DeclineReason::IntegrandNotEnclosable(format!("on {}: {reason}", box_.decimal(12)))
    })
}

/// Rebuild one panel's contribution from the partition alone — the single
/// function the producer and the verifier share.
fn panel_from(
    f: &CasExpr,
    fourth_derivative: &CasExpr,
    var: &str,
    lo: &BigRational,
    hi: &BigRational,
    rule: QuadratureRule,
    order: u32,
) -> Result<IntegralPanel, DeclineReason> {
    let width = hi - lo;
    let span = BigInterval::new(lo.clone(), hi.clone())
        .ok_or_else(|| DeclineReason::IntegrandNotEnclosable("panel is inverted".to_string()))?;
    match rule {
        QuadratureRule::Box => {
            let over = integrand_over(f, var, &span, order)?;
            let value = round_series(&over.scale(&width), order);
            Ok(IntegralPanel {
                lo: lo.clone(),
                hi: hi.clone(),
                at_lo: over,
                at_mid: BigInterval::point(BigRational::zero()),
                at_hi: BigInterval::point(BigRational::zero()),
                fourth: BigInterval::point(BigRational::zero()),
                value,
            })
        }
        QuadratureRule::Simpson => {
            let middle = (lo + hi) / bi(2);
            let at_lo = integrand_over(f, var, &BigInterval::point(lo.clone()), order)?;
            let at_mid = integrand_over(f, var, &BigInterval::point(middle), order)?;
            let at_hi = integrand_over(f, var, &BigInterval::point(hi.clone()), order)?;
            let fourth = integrand_over(fourth_derivative, var, &span, DERIVATIVE_ORDER)?;
            let simpson = at_lo
                .add(&at_mid.scale(&bi(4)))
                .add(&at_hi)
                .scale(&(&width / bi(6)));
            let error = ratpow_big(&width, 5) * sup_abs(&fourth) / bi(2880);
            let value = round_series(
                &BigInterval::new(simpson.lo() - &error, simpson.hi() + &error)
                    .ok_or(DeclineReason::PrecisionUnreachable)?,
                order,
            );
            Ok(IntegralPanel {
                lo: lo.clone(),
                hi: hi.clone(),
                at_lo,
                at_mid,
                at_hi,
                fourth,
                value,
            })
        }
    }
}

/// The enclosure of `∫` over a sliver box: `width · sup abs(f)`, symmetric
/// about zero because the direction of the sliver is not known.
fn edge_from(
    f: &CasExpr,
    var: &str,
    box_: &BigInterval,
    order: u32,
) -> Result<BigInterval, DeclineReason> {
    if box_.width().is_zero() {
        return Ok(BigInterval::point(BigRational::zero()));
    }
    let over = integrand_over(f, var, box_, order)?;
    let bound = box_.width() * sup_abs(&over);
    let symmetric =
        BigInterval::new(-bound.clone(), bound).ok_or(DeclineReason::PrecisionUnreachable)?;
    Ok(round_series(&symmetric, order))
}

/// The dyadic core `[A, B]` of `[a.hi, b.lo]` and the two sliver boxes, or a
/// decline when the limits do not bracket a usable core.
fn core_and_edges(
    lower: &BigInterval,
    upper: &BigInterval,
    bits: u32,
) -> Result<(BigRational, BigRational, BigInterval, BigInterval), DeclineReason> {
    if lower.hi() > upper.lo() {
        return Err(DeclineReason::DomainError(
            "the limits of integration do not bracket a non-empty core".to_string(),
        ));
    }
    let core_lo = dyadic_ceil(lower.hi(), bits);
    let core_hi = dyadic_floor(upper.lo(), bits);
    if core_lo > core_hi {
        return Err(DeclineReason::DomainError(
            "the limits of integration are closer together than the dyadic grid".to_string(),
        ));
    }
    let low_edge = BigInterval::new(lower.lo().clone(), core_lo.clone())
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    let high_edge = BigInterval::new(core_hi.clone(), upper.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    Ok((
        core_lo,
        core_hi,
        coarsen(&low_edge, bits),
        coarsen(&high_edge, bits),
    ))
}

/// The partition points of `[core_lo, core_hi]` into `panels` equal parts, with
/// every interior point on the dyadic grid.
fn partition_points(core_lo: &BigRational, core_hi: &BigRational, panels: u32) -> Vec<BigRational> {
    let count = panels.max(1);
    let step = (core_hi - core_lo) / bi_u64(u64::from(count));
    let mut points = Vec::with_capacity(count as usize + 1);
    points.push(core_lo.clone());
    for index in 1..count {
        points.push(core_lo + &step * bi_u64(u64::from(index)));
    }
    points.push(core_hi.clone());
    points
}

/// A certified enclosure of the definite integral `∫_a^b f dx`, with the
/// quadrature evidence that produced it.
///
/// `a` and `b` are **intervals**, so a limit that is itself only known to an
/// enclosure — `π`, say — is expressible; the uncertainty in each limit is
/// charged as a sliver term `width · sup abs(f)` and the answer contains
/// `∫_a^b f` for every `a` and `b` in those intervals. A point limit
/// contributes exactly zero.
///
/// Returns `None` when no certificate could be produced; use
/// [`enclose_integral_with_reason`] for the obstacle.
///
/// ```
/// use axeyum_cas::CasExpr;
/// use axeyum_cas::enclosure_integral::{enclose_integral, rational_limit};
/// use axeyum_ir::Rational;
/// // ∫₀¹ x² dx = 1/3.
/// let f = CasExpr::var("x").pow(2);
/// let e = enclose_integral(
///     &f,
///     "x",
///     &rational_limit(Rational::integer(0)),
///     &rational_limit(Rational::integer(1)),
///     30,
/// )
/// .unwrap();
/// assert!(e.verify(&f, "x").is_ok());
/// assert!(e.interval.decimal(6).starts_with("[0.333333"));
/// ```
#[must_use]
pub fn enclose_integral(
    f: &CasExpr,
    var: &str,
    a: &BigInterval,
    b: &BigInterval,
    precision: u32,
) -> Option<IntegralEnclosure> {
    enclose_integral_with_reason(f, var, a, b, precision).ok()
}

/// A limit of integration at an exact rational point.
#[must_use]
pub fn rational_limit(value: Rational) -> BigInterval {
    BigInterval::point(from_rational(value))
}

/// [`enclose_integral`], reporting the obstacle when it declines.
///
/// The panel count doubles from `1` until the total width meets
/// `2^(−precision)` or [`MAX_REFINEMENTS`] is exhausted. Simpson is attempted
/// first; if `f⁗` cannot be enclosed over the whole interval the request falls
/// back to the always-sound box rule, and the certificate records which.
///
/// # Errors
///
/// [`DeclineReason::IntegrandNotEnclosable`] when `f` itself cannot be enclosed
/// on a panel — an interior pole, a domain violation, or an unsupported head —
/// naming the panel; [`DeclineReason::DomainError`] when the limits do not
/// bracket a usable core; [`DeclineReason::PrecisionUnreachable`] when the
/// refinement cap is reached without meeting the width bound.
pub fn enclose_integral_with_reason(
    f: &CasExpr,
    var: &str,
    a: &BigInterval,
    b: &BigInterval,
    precision: u32,
) -> Result<IntegralEnclosure, DeclineReason> {
    let order = quadrature_order(precision);
    let bits = quadrature_bits(precision);
    let (core_lo, core_hi, low_box, high_box) = core_and_edges(a, b, bits)?;
    let fourth_derivative = f.differentiate_n(var, 4);
    let target = pow2(-i32::try_from(precision.min(1_000_000)).unwrap_or(i32::MAX));
    // The whole-interval probe decides the rule once, so the certificate names
    // one rule rather than a per-panel mixture.
    let whole = BigInterval::new(core_lo.clone(), core_hi.clone())
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    integrand_over(f, var, &whole, order)?;
    let rule = if integrand_over(&fourth_derivative, var, &whole, DERIVATIVE_ORDER).is_ok() {
        QuadratureRule::Simpson
    } else {
        QuadratureRule::Box
    };
    let low_edge = edge_from(f, var, &low_box, order)?;
    let high_edge = edge_from(f, var, &high_box, order)?;
    let mut count = 1u32;
    for _ in 0..=MAX_REFINEMENTS {
        let points = partition_points(&core_lo, &core_hi, count);
        let mut panels = Vec::with_capacity(points.len() - 1);
        let mut total = low_edge.add(&high_edge);
        for window in points.windows(2) {
            let panel = panel_from(
                f,
                &fourth_derivative,
                var,
                &window[0],
                &window[1],
                rule,
                order,
            )?;
            total = total.add(&panel.value);
            panels.push(panel);
        }
        if total.width() <= target {
            return Ok(IntegralEnclosure {
                interval: total,
                precision,
                rule,
                order,
                lower: a.clone(),
                upper: b.clone(),
                panels,
                low_edge_box: low_box,
                high_edge_box: high_box,
                low_edge,
                high_edge,
            });
        }
        count = count.saturating_mul(2);
    }
    Err(DeclineReason::PrecisionUnreachable)
}

impl IntegralEnclosure {
    /// Re-derive the whole quadrature from the recorded partition and refuse
    /// anything that does not hold up.
    ///
    /// The verifier reads only `(rule, order, lower, upper, precision)` and the
    /// partition endpoints; every evaluation, every panel contribution, every
    /// sliver bound and the total are recomputed from the integrand itself. The
    /// guards, each with a test that dies when it is deleted:
    ///
    /// 1. **empty partition** — a certificate must carry at least one panel;
    /// 2. **partition gap** — consecutive panels must share an endpoint and
    ///    each must have `lo <= hi`, so no stretch of the interval is skipped
    ///    and none is counted twice;
    /// 3. **core coverage** — the first panel must start at or above
    ///    `lower.hi` and the last must end at or below `upper.lo`, and the two
    ///    sliver boxes must cover the gaps that leaves;
    /// 4. **evaluation understated** — each recorded evaluation
    ///    (`at_lo`, `at_mid`, `at_hi`, `fourth`) must contain the recomputed
    ///    one, so a forger cannot narrow an integrand value or a derivative
    ///    bound;
    /// 5. **panel understated** — each recorded `value` must contain the
    ///    contribution recomputed from the recorded endpoints;
    /// 6. **sliver understated** — each recorded edge enclosure must contain
    ///    the recomputed one over the recorded box;
    /// 7. **total understated** — the recorded `interval` must contain the sum
    ///    of the recomputed panels and slivers;
    /// 8. **final width** — the width must not exceed `2^(−precision)`.
    ///
    /// # Errors
    ///
    /// Returns a message naming the guard that fired and the panel it fired on.
    pub fn verify(&self, f: &CasExpr, var: &str) -> Result<(), String> {
        // Guard 1: empty partition.
        let Some(first) = self.panels.first() else {
            return Err("the certificate carries no panels".into());
        };
        let last = self
            .panels
            .last()
            .ok_or_else(|| "the certificate carries no panels".to_string())?;
        // Guard 2: partition gaps and inverted panels.
        for (index, panel) in self.panels.iter().enumerate() {
            if panel.lo > panel.hi {
                return Err(format!("panel {index} has lo above hi"));
            }
            if index > 0 && self.panels[index - 1].hi != panel.lo {
                return Err(format!(
                    "panel {index} does not start where panel {} ended",
                    index - 1
                ));
            }
        }
        // Guard 3: the core sits inside the limits, and the slivers cover the
        // rest.
        if &first.lo < self.lower.hi() || &last.hi > self.upper.lo() {
            return Err("the partition is not inside the limits of integration".into());
        }
        if self.low_edge_box.lo() > self.lower.lo()
            || self.low_edge_box.hi() < &first.lo
            || self.high_edge_box.lo() > &last.hi
            || self.high_edge_box.hi() < self.upper.hi()
        {
            return Err("the sliver boxes do not cover the gap to the limits".into());
        }
        let fourth_derivative = f.differentiate_n(var, 4);
        let mut total = BigInterval::point(BigRational::zero());
        for (index, panel) in self.panels.iter().enumerate() {
            let recomputed = panel_from(
                f,
                &fourth_derivative,
                var,
                &panel.lo,
                &panel.hi,
                self.rule,
                self.order,
            )
            .map_err(|reason| format!("panel {index} does not re-evaluate: {reason}"))?;
            // Guard 4: evaluation understated.
            let claimed = [&panel.at_lo, &panel.at_mid, &panel.at_hi, &panel.fourth];
            let derived = [
                &recomputed.at_lo,
                &recomputed.at_mid,
                &recomputed.at_hi,
                &recomputed.fourth,
            ];
            for (slot, (claim, want)) in claimed.iter().zip(derived).enumerate() {
                if !claim.contains_interval(want) {
                    return Err(format!(
                        "panel {index} evaluation {slot} does not contain the recomputed enclosure"
                    ));
                }
            }
            // Guard 5: panel understated.
            if !panel.value.contains_interval(&recomputed.value) {
                return Err(format!(
                    "panel {index} claims a contribution that does not contain the recomputed one"
                ));
            }
            total = total.add(&recomputed.value);
        }
        // Guard 6: sliver understated.
        let low = edge_from(f, var, &self.low_edge_box, self.order)
            .map_err(|reason| format!("the lower sliver does not re-evaluate: {reason}"))?;
        let high = edge_from(f, var, &self.high_edge_box, self.order)
            .map_err(|reason| format!("the upper sliver does not re-evaluate: {reason}"))?;
        if !self.low_edge.contains_interval(&low) || !self.high_edge.contains_interval(&high) {
            return Err("a sliver enclosure does not contain the recomputed bound".into());
        }
        total = total.add(&low).add(&high);
        // Guard 7: total understated.
        if !self.interval.contains_interval(&total) {
            return Err("the certificate's interval does not contain the recomputed total".into());
        }
        // Guard 8: final width.
        let target = pow2(-i32::try_from(self.precision.min(1_000_000)).unwrap_or(i32::MAX));
        if self.interval.width() > target {
            return Err(format!(
                "final width {} exceeds 2^-{}",
                self.interval.width(),
                self.precision
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enclosure::{Enclosure, StepHead, enclose, enclose_constant, enclose_with_reason};

    /// A decimal literal as an exact rational — used only to state a cited
    /// digit string, never to compute.
    fn decimal_to_rational(text: &str) -> BigRational {
        let (negative, body) = match text.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, text),
        };
        let (whole, fraction) = body.split_once('.').unwrap_or((body, ""));
        let digits = format!("{whole}{fraction}");
        let numerator: BigInt = digits.parse().expect("decimal digits");
        let denominator = BigInt::from(10u32).pow(u32::try_from(fraction.len()).unwrap());
        let value = BigRational::new(numerator, denominator);
        if negative { -value } else { value }
    }

    /// The band `[d, d + 10^-30]` a value truncated to 30 decimals must lie in.
    fn digit_band(truncated: &str) -> BigInterval {
        let lo = decimal_to_rational(truncated);
        let step = BigRational::new(BigInt::one(), BigInt::from(10u32).pow(30));
        BigInterval::new(lo.clone(), lo + step).expect("band")
    }

    // -- The cited digits -------------------------------------------------
    //
    // Every string below is the value **truncated** (not rounded) to 30
    // decimals, so the true value lies in `[d, d + 10^-30]`. Provenance, in two
    // independent layers:
    //
    //  * `GAMMA_30` is OEIS A001620; `PI_SIXTH_30` and `PI_THIRD_30` are OEIS
    //    A000796 over 6 and over 3; `ASINH1_30`, `ACOSH2_30` and
    //    `ATANH_HALF_30` are `ln(1+√2)`, `ln(2+√3)` and `ln(3)/2`.
    //  * the rest were recomputed independently in Python's `decimal` at 70
    //    digits from the defining series — a different language, a different
    //    arithmetic, and code that shares nothing with the producer under test
    //    — and each agrees with its published value where one is tabulated:
    //    `Si(1)` A099281, `Ci(1)` A099284, `Ei(1)` A091725, `li(2)` A069284,
    //    and `∫₀¹e^(−x²) = √π·erf(1)/2`.
    //
    // A mismatch against these means the **enclosure** is wrong; the digit
    // strings are the cited authority, not the output.
    const GAMMA_30: &str = "0.577215664901532860606512090082";
    const SI_ONE_30: &str = "0.946083070367183014941353313823";
    const CI_ONE_30: &str = "0.337403922900968134662646203889";
    const EI_ONE_30: &str = "1.895117816355936755466520934331";
    const LI_TWO_30: &str = "1.045163780117492784844588889194";
    const SHI_ONE_30: &str = "1.057250875375728514571842354895";
    const CHI_ONE_30: &str = "0.837866940980208240894678579435";
    const FRESNEL_C_ONE_30: &str = "0.779893400376822829474206413652";
    const FRESNEL_S_ONE_30: &str = "0.438259147390354766076756696625";
    const PI_SIXTH_30: &str = "0.523598775598298873077107230546";
    const PI_THIRD_30: &str = "1.047197551196597746154214461093";
    const ASINH1_30: &str = "0.881373587019543025232609324979";
    const ACOSH2_30: &str = "1.316957896924816708625046347307";
    const ATANH_HALF_30: &str = "0.549306144334054845697622618461";
    const GAUSS_30: &str = "0.746824132812427025399467436131";

    /// The precision every 30-digit test asks for. `2^-110` is about `7.7e-34`,
    /// three orders of magnitude inside a `1e-30` band, and it keeps the heads
    /// on the order-64 rung of the ladder rather than the order-128 one — which
    /// is the difference between a two-second test and a seven-second one in a
    /// debug build.
    const DIGIT_PRECISION: u32 = 105;

    fn unary(func: UnaryFunc, argument: CasExpr) -> CasExpr {
        CasExpr::Unary(func, Box::new(argument))
    }

    /// Enclose `expr`, check it verifies, and check it sits inside the cited
    /// 30-digit band.
    fn check_digits(expr: &CasExpr, cited: &str) -> Enclosure {
        let enclosure =
            enclose(expr, &[], DIGIT_PRECISION).unwrap_or_else(|| panic!("no enclosure: {expr:?}"));
        enclosure
            .verify(expr, &[])
            .unwrap_or_else(|e| panic!("{expr:?} does not verify: {e}"));
        assert!(
            digit_band(cited).contains_interval(&enclosure.interval),
            "{expr:?} encloses to {} which is outside the cited digits {cited}",
            enclosure.interval.decimal(32)
        );
        enclosure
    }

    // -- Euler's constant --------------------------------------------------

    #[test]
    fn euler_gamma_meets_the_cited_digits_and_verifies() {
        let expr = CasExpr::var(crate::enclosure::EULER_GAMMA_NAME);
        check_digits(&expr, GAMMA_30);
        let constant = enclose_constant("euler_gamma", DIGIT_PRECISION).expect("gamma");
        assert!(digit_band(GAMMA_30).contains_interval(&constant.interval));
        let alias = enclose_constant("gamma", DIGIT_PRECISION).expect("gamma alias");
        assert_eq!(alias.interval, constant.interval);
    }

    #[test]
    fn euler_gamma_is_a_pure_function_of_its_order() {
        // The memo table must change the cost and not the value: the second
        // call comes from the cache, the third from a fresh computation.
        let first = euler_gamma(32).expect("gamma at 32");
        let second = euler_gamma(32).expect("gamma at 32 again");
        assert_eq!(first, second);
        assert_eq!(first, euler_gamma_uncached(32).expect("uncached"));
    }

    #[test]
    fn euler_gamma_narrows_as_the_order_climbs() {
        let coarse = euler_gamma(4).expect("gamma at 4");
        let fine = euler_gamma(64).expect("gamma at 64");
        assert!(
            fine.width() < coarse.width(),
            "gamma at order 64 ({}) is not narrower than at order 4 ({})",
            fine.width(),
            coarse.width()
        );
        assert!(coarse.contains(fine.lo()), "the two orders disagree");
    }

    // -- The integral-defined heads ---------------------------------------

    #[test]
    fn si_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Si, CasExpr::int(1)), SI_ONE_30);
    }

    #[test]
    fn ci_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Ci, CasExpr::int(1)), CI_ONE_30);
    }

    #[test]
    fn ei_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Ei, CasExpr::int(1)), EI_ONE_30);
    }

    #[test]
    fn li_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Li, CasExpr::int(2)), LI_TWO_30);
    }

    #[test]
    fn shi_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Shi, CasExpr::int(1)), SHI_ONE_30);
    }

    #[test]
    fn chi_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Chi, CasExpr::int(1)), CHI_ONE_30);
    }

    #[test]
    fn the_fresnel_cosine_integral_meets_the_cited_digits() {
        check_digits(
            &unary(UnaryFunc::FresnelC, CasExpr::int(1)),
            FRESNEL_C_ONE_30,
        );
    }

    #[test]
    fn the_fresnel_sine_integral_meets_the_cited_digits() {
        check_digits(
            &unary(UnaryFunc::FresnelS, CasExpr::int(1)),
            FRESNEL_S_ONE_30,
        );
    }

    #[test]
    fn asin_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Asin, CasExpr::rat(1, 2)), PI_SIXTH_30);
    }

    #[test]
    fn acos_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Acos, CasExpr::rat(1, 2)), PI_THIRD_30);
    }

    #[test]
    fn asin_reduces_near_one_instead_of_grinding() {
        // asin(1) = pi/2 exactly, through the half-angle reduction whose inner
        // argument is 0; asin(9/10) exercises the reduction proper.
        let half_pi = enclose_constant("pi", 60)
            .expect("pi")
            .interval
            .scale(&br(1, 2));
        let at_one = enclose(&unary(UnaryFunc::Asin, CasExpr::int(1)), &[], 60).expect("asin 1");
        assert!(
            at_one.interval.hi() >= half_pi.lo() && at_one.interval.lo() <= half_pi.hi(),
            "asin(1) = {} does not meet pi/2 = {}",
            at_one.interval.decimal(20),
            half_pi.decimal(20)
        );
        let near =
            enclose(&unary(UnaryFunc::Asin, CasExpr::rat(9, 10)), &[], 60).expect("asin 9/10");
        // asin(0.9) = 1.1197695149986341866866770558...
        assert!(
            near.interval.decimal(12).starts_with("[1.119769514998"),
            "asin(9/10) = {}",
            near.interval.decimal(16)
        );
    }

    #[test]
    fn asinh_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Asinh, CasExpr::int(1)), ASINH1_30);
    }

    #[test]
    fn acosh_meets_the_cited_digits() {
        check_digits(&unary(UnaryFunc::Acosh, CasExpr::int(2)), ACOSH2_30);
    }

    #[test]
    fn asinh_is_odd_and_acosh_is_zero_at_one() {
        let positive =
            enclose(&unary(UnaryFunc::Asinh, CasExpr::int(3)), &[], 60).expect("asinh 3");
        let negative =
            enclose(&unary(UnaryFunc::Asinh, CasExpr::int(-3)), &[], 60).expect("asinh -3");
        let mirrored = positive.interval.negate();
        assert!(
            mirrored.hi() >= negative.interval.lo() && mirrored.lo() <= negative.interval.hi(),
            "asinh is not odd: {} vs {}",
            mirrored.decimal(20),
            negative.interval.decimal(20)
        );
        let at_one = enclose(&unary(UnaryFunc::Acosh, CasExpr::int(1)), &[], 60).expect("acosh 1");
        assert!(at_one.interval.contains(&BigRational::zero()));
    }

    #[test]
    fn atanh_is_built_from_the_certified_logarithm() {
        let expr = atanh_expr(CasExpr::rat(1, 2));
        check_digits(&expr, ATANH_HALF_30);
        // It is a constructor, not a head: the certificate goes through `ln`.
        let enclosure = enclose(&expr, &[], 40).expect("atanh");
        assert!(
            enclosure
                .evidence
                .iter()
                .any(|step| step.head == StepHead::Ln),
            "the atanh certificate does not go through `ln`"
        );
    }

    // -- Declines ----------------------------------------------------------

    #[test]
    fn the_integral_heads_decline_outside_their_domains() {
        let cases: Vec<(CasExpr, &str)> = vec![
            (unary(UnaryFunc::Ci, CasExpr::int(-1)), "Ci"),
            (unary(UnaryFunc::Chi, CasExpr::int(0)), "Chi"),
            (unary(UnaryFunc::Ei, CasExpr::int(0)), "Ei"),
            (unary(UnaryFunc::Li, CasExpr::int(1)), "li"),
            (unary(UnaryFunc::Li, CasExpr::int(-2)), "li"),
            (unary(UnaryFunc::Asin, CasExpr::int(2)), "asin"),
            (unary(UnaryFunc::Acos, CasExpr::int(-3)), "asin"),
            (unary(UnaryFunc::Acosh, CasExpr::rat(1, 2)), "acosh"),
        ];
        for (expr, label) in cases {
            match enclose_with_reason(&expr, &[], 30) {
                Err(DeclineReason::DomainError(message)) => {
                    assert!(
                        message.contains(label),
                        "the decline `{message}` does not name `{label}`"
                    );
                }
                other => panic!("{label} did not decline with a domain error: {other:?}"),
            }
        }
    }

    #[test]
    fn the_series_heads_decline_past_their_magnitude_limit() {
        let beyond = CasExpr::int(i128::from(SERIES_MAGNITUDE_LIMIT) + 1);
        for func in [UnaryFunc::Si, UnaryFunc::Shi, UnaryFunc::FresnelC] {
            assert!(
                matches!(
                    enclose_with_reason(&unary(func, beyond.clone()), &[], 20),
                    Err(DeclineReason::ResourceLimit)
                ),
                "{func:?} did not decline past the magnitude limit"
            );
        }
        // ...and answers at the limit itself, so the decline is about the
        // magnitude and not about the head.
        assert!(
            enclose(
                &unary(
                    UnaryFunc::Si,
                    CasExpr::int(i128::from(SERIES_MAGNITUDE_LIMIT))
                ),
                &[],
                20
            )
            .is_some(),
            "Si declines at the magnitude limit itself"
        );
    }

    #[test]
    fn the_alternating_bound_is_refused_below_its_monotonicity_index() {
        // The hypothesis is not assumed: at magnitude 10 the Si terms are still
        // growing at index 3, so the kernel declines that order outright and
        // only the ladder's higher orders answer.
        let argument = BigInterval::point(bi(10));
        assert!(odd_series_index(&bi(10)).expect("index") > 3);
        assert!(matches!(
            si_interval(&argument, 3),
            Err(DeclineReason::PrecisionUnreachable)
        ));
        assert!(si_interval(&argument, 32).is_ok());
    }

    #[test]
    fn the_geometric_majorant_is_refused_while_its_ratio_is_large() {
        // Shi has positive terms, so its tail needs a geometric majorant
        // `t_(n+1)/(1 − R)`. That is valid for any `R < 1`; the module refuses
        // at `R >= 1/2` instead, so the majorant is never marginal. Both halves
        // of that sentence need a control, and they fail differently — the
        // first version of this test had only the first case and the guard
        // deletion SURVIVED it:
        //
        //  * at magnitude 10 and order 2 the ratio exceeds 1, so `1 − R` is
        //    negative and the interval constructor refuses on its own. Deleting
        //    the guard still declines here, so this case alone measures
        //    nothing about the guard;
        //  * at magnitude 15/2 and order 2 the ratio is 0.607, inside
        //    `[1/2, 1)`: the majorant is mathematically valid there and only
        //    the module's own margin refuses it. This is the case that dies
        //    when the guard is deleted.
        let far = BigInterval::point(bi(10));
        assert!(
            odd_series_ratio(&bi(10), 3) >= BigRational::one(),
            "the runaway control needs a ratio at or above 1"
        );
        assert!(matches!(
            shi_interval(&far, 2),
            Err(DeclineReason::PrecisionUnreachable)
        ));
        let margin = BigInterval::point(br(15, 2));
        let ratio = odd_series_ratio(&br(15, 2), 3);
        assert!(
            ratio >= br(1, 2) && ratio < BigRational::one(),
            "the margin control needs a ratio in [1/2, 1), got {ratio}"
        );
        assert!(matches!(
            shi_interval(&margin, 2),
            Err(DeclineReason::PrecisionUnreachable)
        ));
        // ...and a high enough order answers in both cases, so neither decline
        // is about the argument.
        assert!(shi_interval(&far, 32).is_ok());
        assert!(shi_interval(&margin, 32).is_ok());
    }

    #[test]
    fn a_forged_euler_gamma_step_is_refused() {
        let expr = CasExpr::var(crate::enclosure::EULER_GAMMA_NAME);
        let honest = enclose(&expr, &[], 40).expect("gamma");
        // Halving the recorded remainder understates the method's own error.
        let mut forged = honest.clone();
        forged.evidence[0].remainder = &forged.evidence[0].remainder / bi(2);
        assert!(forged.verify(&expr, &[]).is_err());
        // Narrowing the output to a point inside the honest interval breaks
        // containment of the recomputed enclosure.
        let mut narrowed = honest.clone();
        narrowed.evidence[0].output = BigInterval::point(honest.interval.midpoint());
        narrowed.interval = narrowed.evidence[0].output.clone();
        assert!(narrowed.verify(&expr, &[]).is_err());
        // And a step claiming to be `pi` instead is caught by the head guard.
        let mut relabelled = honest;
        relabelled.evidence[0].head = StepHead::Pi;
        assert!(relabelled.verify(&expr, &[]).is_err());
    }

    // -- Symbolic exponents ------------------------------------------------

    #[test]
    fn a_symbolic_exponent_agrees_with_the_root_route() {
        let through_exp = symbolic_power(CasExpr::int(2), CasExpr::rat(1, 3));
        let through_root = crate::enclosure::rational_power(CasExpr::int(2), 1, 3).expect("root");
        let a = enclose(&through_exp, &[], 80).expect("exp route");
        let b = enclose(&through_root, &[], 80).expect("root route");
        a.verify(&through_exp, &[]).expect("exp route verifies");
        b.verify(&through_root, &[]).expect("root route verifies");
        assert!(
            a.interval.hi() >= b.interval.lo() && a.interval.lo() <= b.interval.hi(),
            "the two routes to 2^(1/3) do not overlap: {} vs {}",
            a.interval.decimal(30),
            b.interval.decimal(30)
        );
    }

    #[test]
    fn a_symbolic_exponent_may_be_an_interval_variable() {
        // The exponent is a bound variable over a box, not a literal: 2^y for y
        // in [1, 1 + 2^-20] must contain 2, and its width must respect the
        // requested precision — which is what forces the box to be narrow, since
        // `enclose` guarantees the width of the ANSWER.
        let expr = symbolic_power(CasExpr::int(2), CasExpr::var("y"));
        let step = Rational::checked_new(1, 1 << 20).expect("step");
        let binding = Interval::new(
            Rational::integer(1),
            Rational::integer(1).checked_add(step).expect("upper"),
        )
        .expect("interval");
        let enclosure = enclose(&expr, &[("y", binding)], 8).expect("2^y");
        enclosure
            .verify(&expr, &[("y", binding)])
            .expect("verifies");
        assert!(
            enclosure.interval.contains(&bi(2)),
            "2^y over [1, 1+2^-20] = {} does not contain 2",
            enclosure.interval.decimal(12)
        );
        // The box really propagated: the answer is an interval, not a point,
        // and it does not reach the value at the far end of a wide box.
        assert!(
            !enclosure.interval.width().is_zero(),
            "the binding box did not propagate through the exponent"
        );
        assert!(!enclosure.interval.contains(&bi(4)));
    }

    #[test]
    fn a_non_positive_base_declines_with_a_reason_naming_pow() {
        for base in [CasExpr::int(-2), CasExpr::int(0)] {
            match enclose_symbolic_power(&base, &CasExpr::rat(1, 2), &[], 30) {
                Err(DeclineReason::DomainError(message)) => {
                    assert!(
                        message.contains("pow"),
                        "the decline `{message}` does not name pow"
                    );
                }
                other => panic!("a non-positive base did not decline: {other:?}"),
            }
        }
        // A straddling base declines too, and a positive one does not.
        let straddling = Interval::new(Rational::integer(-1), Rational::integer(1)).expect("iv");
        assert!(matches!(
            enclose_symbolic_power(
                &CasExpr::var("x"),
                &CasExpr::int(2),
                &[("x", straddling)],
                8
            ),
            Err(DeclineReason::DomainError(_))
        ));
        assert!(enclose_symbolic_power(&CasExpr::int(3), &CasExpr::rat(1, 2), &[], 30).is_ok());
    }

    // -- Definite integrals -------------------------------------------------

    fn at(value: i64) -> BigInterval {
        BigInterval::point(bi(value))
    }

    #[test]
    fn the_integral_of_x_squared_over_the_unit_interval_is_one_third() {
        let f = CasExpr::var("x").pow(2);
        let e = enclose_integral(&f, "x", &at(0), &at(1), 30).expect("integral");
        e.verify(&f, "x").expect("verifies");
        assert_eq!(e.rule, QuadratureRule::Simpson);
        assert!(
            e.interval.contains(&br(1, 3)),
            "the enclosure {} does not contain 1/3",
            e.interval.decimal(40)
        );
    }

    #[test]
    fn the_gaussian_integral_meets_its_cited_digits() {
        let f = CasExpr::Unary(
            UnaryFunc::Exp,
            Box::new(CasExpr::Neg(Box::new(CasExpr::var("x").pow(2)))),
        );
        let e = enclose_integral(&f, "x", &at(0), &at(1), 20).expect("integral");
        e.verify(&f, "x").expect("verifies");
        let cited = decimal_to_rational(GAUSS_30);
        assert!(
            e.interval.contains(&cited),
            "the enclosure {} does not contain the cited {GAUSS_30}",
            e.interval.decimal(34)
        );
    }

    #[test]
    fn the_integral_of_sine_over_a_half_period_is_two() {
        let f = CasExpr::var("x").sin();
        let pi = enclose_constant("pi", 60).expect("pi").interval;
        let e = enclose_integral(&f, "x", &at(0), &pi, 16).expect("integral");
        e.verify(&f, "x").expect("verifies");
        assert!(
            e.interval.contains(&bi(2)),
            "the enclosure {} does not contain 2",
            e.interval.decimal(30)
        );
    }

    #[test]
    fn an_integrand_with_an_interior_pole_declines_with_its_own_reason() {
        // 1/(x−1) on [0, 2].
        let f = CasExpr::Div(
            Box::new(CasExpr::int(1)),
            Box::new(CasExpr::Add(vec![CasExpr::var("x"), CasExpr::int(-1)])),
        );
        match enclose_integral_with_reason(&f, "x", &at(0), &at(2), 10) {
            Err(DeclineReason::IntegrandNotEnclosable(message)) => {
                assert!(
                    message.contains("divisor"),
                    "the decline `{message}` does not name the obstacle"
                );
            }
            other => panic!("the pole did not decline distinctly: {other:?}"),
        }
        // The same integrand away from the pole is fine, so the decline is
        // about the pole and not about the shape of the expression.
        assert!(enclose_integral(&f, "x", &at(2), &at(3), 10).is_some());
    }

    #[test]
    fn the_box_rule_takes_over_when_the_fourth_derivative_is_not_enclosable() {
        // sqrt(x) on [0, 1]: `f` encloses, `f''''` divides by an interval
        // reaching 0, so Simpson is unavailable and the always-sound box rule
        // answers. The exact value is 2/3.
        // `NthRoot(2)` rather than `Sqrt`: the same function, but its kernel
        // rounds each Newton iterate onto the dyadic grid, where `sqrt_point`
        // still lets the iterate double in size to a 2048-bit floor. Over the
        // 511 panel evaluations this refinement needs, that is the difference
        // between a second and several minutes.
        let f = CasExpr::Unary(UnaryFunc::NthRoot(2), Box::new(CasExpr::var("x")));
        // Precision 6, not 30: the box rule converges LINEARLY, so the panel
        // count is `2^precision` and the cost of this test is exponential in it.
        // That is the rule's stated weakness, not an accident of the fixture.
        let e = enclose_integral(&f, "x", &at(0), &at(1), 6).expect("integral");
        e.verify(&f, "x").expect("verifies");
        assert_eq!(e.rule, QuadratureRule::Box);
        assert!(
            e.interval.contains(&br(2, 3)),
            "the enclosure {} does not contain 2/3",
            e.interval.decimal(12)
        );
    }

    #[test]
    fn a_point_limit_charges_no_sliver_and_an_interval_limit_does() {
        let f = CasExpr::int(1);
        let exact = enclose_integral(&f, "x", &at(0), &at(1), 30).expect("integral");
        assert!(exact.low_edge.width().is_zero());
        assert!(exact.high_edge.width().is_zero());
        let fuzzy_upper = BigInterval::new(bi(1), bi(1) + pow2(-40)).expect("fuzzy");
        let fuzzy = enclose_integral(&f, "x", &at(0), &fuzzy_upper, 30).expect("integral");
        fuzzy.verify(&f, "x").expect("verifies");
        assert!(!fuzzy.high_edge.width().is_zero());
        assert!(fuzzy.interval.contains(&BigRational::one()));
    }

    // -- The quadrature verifier's guards ----------------------------------

    /// A small honest certificate to forge against.
    fn honest_integral() -> (CasExpr, IntegralEnclosure) {
        let f = CasExpr::var("x").pow(2);
        let e = enclose_integral(&f, "x", &at(0), &at(1), 30).expect("integral");
        (f, e)
    }

    /// The same certificate cut into two contiguous panels, so a gap between
    /// them is expressible.
    fn honest_two_panels() -> (CasExpr, IntegralEnclosure) {
        let (f, mut e) = honest_integral();
        while e.panels.len() < 2 {
            let derivative = f.differentiate_n("x", 4);
            let mut split = Vec::new();
            for panel in &e.panels {
                let middle = (&panel.lo + &panel.hi) / bi(2);
                split.push(
                    panel_from(&f, &derivative, "x", &panel.lo, &middle, e.rule, e.order)
                        .expect("left panel"),
                );
                split.push(
                    panel_from(&f, &derivative, "x", &middle, &panel.hi, e.rule, e.order)
                        .expect("right panel"),
                );
            }
            let mut total = e.low_edge.add(&e.high_edge);
            for panel in &split {
                total = total.add(&panel.value);
            }
            e.interval = total;
            e.panels = split;
        }
        e.verify(&f, "x").expect("the two-panel form is honest");
        (f, e)
    }

    #[test]
    fn guard_one_refuses_an_empty_partition() {
        let (f, mut e) = honest_integral();
        e.panels.clear();
        let message = e
            .verify(&f, "x")
            .expect_err("an empty partition must be refused");
        assert!(message.contains("no panels"), "{message}");
    }

    #[test]
    fn guard_two_refuses_a_partition_gap() {
        // The second panel is moved up AND recomputed honestly at its new
        // endpoints, and the total is the honest sum of what is left. Every
        // other guard therefore passes: each panel contains its own recomputed
        // contribution, each sliver is honest, and the interval contains the
        // sum. The only thing wrong with this certificate is that the stretch
        // `[mid, mid + 2^-8]` is covered by nothing — which is exactly what the
        // partition guard exists to see, and nothing else can.
        let (f, mut e) = honest_two_panels();
        let derivative = f.differentiate_n("x", 4);
        let moved = &e.panels[1].lo + pow2(-8);
        e.panels[1] = panel_from(
            &f,
            &derivative,
            "x",
            &moved,
            &e.panels[1].hi.clone(),
            e.rule,
            e.order,
        )
        .expect("the moved panel");
        let mut total = e.low_edge.add(&e.high_edge);
        for panel in &e.panels {
            total = total.add(&panel.value);
        }
        e.interval = total;
        let message = e.verify(&f, "x").expect_err("a gap must be refused");
        assert!(message.contains("does not start where"), "{message}");
    }

    #[test]
    fn guard_two_refuses_an_inverted_panel() {
        let (f, mut e) = honest_integral();
        let panel = &mut e.panels[0];
        std::mem::swap(&mut panel.lo, &mut panel.hi);
        assert!(
            e.panels[0].lo > e.panels[0].hi,
            "the swap did not invert the panel, so this control is vacuous"
        );
        let message = e.verify(&f, "x").expect_err("inversion must be refused");
        // Deliberately NOT the word `panel_from` uses for the same condition:
        // if this guard is deleted the panel still fails to re-evaluate, and an
        // assertion on shared wording would pass on the fallback and leave this
        // control unable to fail.
        assert!(message.contains("lo above hi"), "{message}");
    }

    #[test]
    fn guard_three_refuses_a_partition_outside_the_limits() {
        let (f, mut e) = honest_integral();
        e.lower = BigInterval::new(bi(0), br(1, 2)).expect("wide lower");
        let message = e
            .verify(&f, "x")
            .expect_err("a partition starting below the lower limit must be refused");
        assert!(message.contains("not inside the limits"), "{message}");
    }

    #[test]
    fn guard_three_refuses_a_sliver_box_that_covers_nothing() {
        let (f, mut e) = honest_integral();
        e.low_edge_box = BigInterval::point(br(1, 4));
        let message = e
            .verify(&f, "x")
            .expect_err("a sliver box that covers nothing must be refused");
        assert!(message.contains("do not cover the gap"), "{message}");
    }

    #[test]
    fn guard_four_refuses_a_narrowed_evaluation() {
        let (f, mut e) = honest_integral();
        // The honest `fourth` for x² is the point 0; a claim of [1, 2] does not
        // contain it.
        e.panels[0].fourth = BigInterval::new(bi(1), bi(2)).expect("forged");
        let message = e
            .verify(&f, "x")
            .expect_err("a narrowed evaluation must be refused");
        assert!(message.contains("evaluation"), "{message}");
    }

    #[test]
    fn guard_five_refuses_a_narrowed_panel_contribution() {
        let (f, mut e) = honest_integral();
        e.panels[0].value = BigInterval::point(bi(0));
        let message = e
            .verify(&f, "x")
            .expect_err("a narrowed panel must be refused");
        assert!(message.contains("contribution"), "{message}");
    }

    #[test]
    fn guard_six_refuses_a_narrowed_sliver() {
        let f = CasExpr::int(1);
        let fuzzy_upper = BigInterval::new(bi(1), bi(1) + pow2(-40)).expect("fuzzy");
        let mut e = enclose_integral(&f, "x", &at(0), &fuzzy_upper, 30).expect("integral");
        e.verify(&f, "x").expect("honest");
        e.high_edge = BigInterval::point(BigRational::zero());
        let message = e
            .verify(&f, "x")
            .expect_err("a narrowed sliver must be refused");
        assert!(message.contains("sliver"), "{message}");
    }

    #[test]
    fn guard_seven_refuses_a_total_that_does_not_contain_the_panels() {
        let (f, mut e) = honest_integral();
        e.interval = BigInterval::new(bi(0), br(1, 100)).expect("forged total");
        let message = e
            .verify(&f, "x")
            .expect_err("a total missing its panels must be refused");
        assert!(message.contains("recomputed total"), "{message}");
    }

    #[test]
    fn guard_eight_refuses_an_over_wide_answer() {
        let (f, mut e) = honest_integral();
        e.interval = BigInterval::new(bi(0), bi(1)).expect("wide");
        let message = e
            .verify(&f, "x")
            .expect_err("an over-wide answer must be refused");
        assert!(message.contains("final width"), "{message}");
    }

    #[test]
    fn the_quadrature_verifier_recomputes_rather_than_reads() {
        // Verification must fail against a *different* integrand even though
        // every recorded number is internally consistent.
        let (_, e) = honest_integral();
        let other = CasExpr::var("x").pow(3);
        assert!(e.verify(&other, "x").is_err());
    }

    // -- Cost --------------------------------------------------------------

    /// ADVISORY ONLY — a single unpinned run per row on a shared host. Run with
    /// `--release --nocapture` to regenerate the table in [`crate::enclosure`].
    #[test]
    fn cost_table_wave_three() {
        use std::time::Instant;
        if let Ok(loadavg) = std::fs::read_to_string("/proc/loadavg") {
            println!("host load average: {}", loadavg.trim());
        }
        println!("head | precision | produce | verify");
        let cases: Vec<(&str, CasExpr)> = vec![
            (
                "euler_gamma",
                CasExpr::var(crate::enclosure::EULER_GAMMA_NAME),
            ),
            ("Si(1)", unary(UnaryFunc::Si, CasExpr::int(1))),
            ("Ci(1)", unary(UnaryFunc::Ci, CasExpr::int(1))),
            ("Ei(1)", unary(UnaryFunc::Ei, CasExpr::int(1))),
            ("FresnelC(1)", unary(UnaryFunc::FresnelC, CasExpr::int(1))),
            ("asin(1/2)", unary(UnaryFunc::Asin, CasExpr::rat(1, 2))),
            ("asinh(1)", unary(UnaryFunc::Asinh, CasExpr::int(1))),
            (
                "2^(1/2) via exp ln",
                symbolic_power(CasExpr::int(2), CasExpr::rat(1, 2)),
            ),
        ];
        let precisions: &[u32] = if cfg!(debug_assertions) {
            &[10, 50]
        } else {
            &[10, 50, 100]
        };
        for (name, expr) in &cases {
            for precision in precisions {
                let start = Instant::now();
                let Some(enclosure) = enclose(expr, &[], *precision) else {
                    println!("{name} | {precision} | declined |");
                    continue;
                };
                let produce = start.elapsed();
                let start = Instant::now();
                enclosure.verify(expr, &[]).expect("verifies");
                println!(
                    "{name} | {precision} | {:?} | {:?}",
                    produce,
                    start.elapsed()
                );
            }
        }
        let f = CasExpr::Unary(
            UnaryFunc::Exp,
            Box::new(CasExpr::Neg(Box::new(CasExpr::var("x").pow(2)))),
        );
        let integral_precisions: &[u32] = if cfg!(debug_assertions) {
            &[10, 16]
        } else {
            &[10, 20, 30]
        };
        for precision in integral_precisions.iter().copied() {
            let start = Instant::now();
            let Some(e) = enclose_integral(&f, "x", &at(0), &at(1), precision) else {
                println!("int exp(-x^2) | {precision} | declined |");
                continue;
            };
            let produce = start.elapsed();
            let start = Instant::now();
            e.verify(&f, "x").expect("verifies");
            println!(
                "int exp(-x^2) | {precision} | {:?} | {:?} | {} panels",
                produce,
                start.elapsed(),
                e.panels.len()
            );
        }
    }
}
