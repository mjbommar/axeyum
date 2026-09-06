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
use crate::enclosure_special::{bernoulli_table, coarsen, dyadic_ceil, dyadic_floor, grid_bits};
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

/// The search cap for a monotonicity or ratio index, matching the parent
/// modules' `SHIFT_CAP`.
const INDEX_CAP: u32 = 4096;

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
        .add(&BigInterval::point(
            BigRational::one() / (bi(2) * &anchor),
        ));
    for j in 1..=terms {
        let index = 2 * usize::try_from(j).ok()?;
        let term = &bernoulli[index] / (bi_u64(index as u64) * ratpow_big(&anchor, 2 * j));
        total = total.add(&BigInterval::point(term));
    }
    let last = 2 * usize::try_from(terms).ok()?;
    let error = (&bernoulli[last]
        / (bi_u64(last as u64) * ratpow_big(&anchor, 2 * terms)))
    .abs();
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

/// The largest absolute value the interval reaches.
fn magnitude(x: &BigInterval) -> BigRational {
    rmax(x.lo().abs(), x.hi().abs())
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
    let square = x.pow(2);
    let mut power = x.clone();
    let mut factorial = BigRational::one();
    let mut sum = x.clone();
    let mut sign = if alternating { -1i64 } else { 1i64 };
    for k in 1..=order {
        let k64 = u64::from(k);
        power = power.mul(&square);
        factorial *= bi_u64(2 * k64) * bi_u64(2 * k64 + 1);
        let coefficient = bi(sign) / (bi_u64(2 * k64 + 1) * &factorial);
        sum = sum.add(&power.scale(&coefficient));
        if alternating {
            sign = -sign;
        }
    }
    let next = u64::from(order) + 1;
    let next_factorial = &factorial * bi_u64(2 * next) * bi_u64(2 * next + 1);
    let omitted =
        ratpow_big(a, 2 * order + 3) / (bi_u64(2 * next + 1) * next_factorial);
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
    BigInterval::new(sum.lo() - &tail, sum.hi() + &tail)
        .ok_or(DeclineReason::PrecisionUnreachable)
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
    (a * a) * bi_u64(2 * k64)
        / (bi_u64(2 * k64 + 1) * bi_u64(2 * k64 + 2) * bi_u64(2 * k64 + 2))
}

/// The partial sum `Σ_(k=1)^order sign^k x^(2k)/(2k·(2k)!)` over an interval,
/// and the magnitude of the first omitted term at `a`.
fn even_partial_sum(
    x: &BigInterval,
    a: &BigRational,
    order: u32,
    alternating: bool,
) -> (BigInterval, BigRational) {
    let square = x.pow(2);
    let mut power = BigInterval::point(BigRational::one());
    let mut factorial = BigRational::one();
    let mut sum = BigInterval::point(BigRational::zero());
    let mut sign = 1i64;
    for k in 1..=order.max(1) {
        let k64 = u64::from(k);
        power = power.mul(&square);
        factorial *= bi_u64(2 * k64 - 1) * bi_u64(2 * k64);
        if alternating {
            sign = -sign;
        }
        let coefficient = bi(sign) / (bi_u64(2 * k64) * &factorial);
        sum = sum.add(&power.scale(&coefficient));
    }
    let count = order.max(1);
    let next = u64::from(count) + 1;
    let next_factorial = &factorial * bi_u64(2 * next - 1) * bi_u64(2 * next);
    let omitted = ratpow_big(a, 2 * count + 2) / (bi_u64(2 * next) * next_factorial);
    (sum, omitted)
}

/// `γ + ln x` over a strictly positive interval — the non-series half of `Ci`
/// and `Chi`.
fn log_and_gamma(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    let low = ln_point(x.lo(), order).ok_or(DeclineReason::ResourceLimit)?;
    let high = ln_point(x.hi(), order).ok_or(DeclineReason::ResourceLimit)?;
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
    let ratio = &a / bi_u64(u64::from(order) + 2);
    if ratio >= br(1, 2) {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let mut power = BigInterval::point(BigRational::one());
    let mut factorial = BigRational::one();
    let mut sum = BigInterval::point(BigRational::zero());
    for k in 1..=order.max(1) {
        let k64 = u64::from(k);
        power = power.mul(x);
        factorial *= bi_u64(k64);
        let coefficient = BigRational::one() / (bi_u64(k64) * &factorial);
        sum = sum.add(&power.scale(&coefficient));
    }
    let count = order.max(1);
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
    let low = ln_point(x.lo(), order).ok_or(DeclineReason::ResourceLimit)?;
    let high = ln_point(x.hi(), order).ok_or(DeclineReason::ResourceLimit)?;
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
    let bound = half.hi().clone();
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
    let half_square = half.pow(2);
    let fourth = x.pow(4);
    let mut coefficient = BigInterval::point(BigRational::one());
    let mut power = x.clone();
    let mut factorial = BigRational::one();
    let mut sum = x.clone();
    let mut sign = -1i64;
    for k in 1..=order {
        let k64 = u64::from(k);
        coefficient = coefficient.mul(&half_square);
        power = power.mul(&fourth);
        factorial *= bi_u64(2 * k64 - 1) * bi_u64(2 * k64);
        let scale = bi(sign) / (&factorial * bi_u64(4 * k64 + 1));
        sum = sum.add(&coefficient.mul(&power).scale(&scale));
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
    let half_square = half.pow(2);
    let fourth = x.pow(4);
    let cube = x.pow(3);
    let mut coefficient = half.clone();
    let mut power = cube;
    let mut factorial = BigRational::one();
    let mut sum = coefficient.mul(&power).scale(&br(1, 3));
    let mut sign = -1i64;
    for k in 1..=order {
        let k64 = u64::from(k);
        coefficient = coefficient.mul(&half_square);
        power = power.mul(&fourth);
        factorial *= bi_u64(2 * k64) * bi_u64(2 * k64 + 1);
        let scale = bi(sign) / (&factorial * bi_u64(4 * k64 + 3));
        sum = sum.add(&coefficient.mul(&power).scale(&scale));
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
        let root = crate::enclosure_special::nth_root_point(&inner, 2, order)?;
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
    BigInterval::new(low.lo().clone(), high.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)
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
    let root = crate::enclosure_special::nth_root_point(&radicand, 2, order)?;
    let argument = root.add(&BigInterval::point(a));
    let low = crate::enclosure_special::ln_large(argument.lo(), order)?;
    let high = crate::enclosure_special::ln_large(argument.hi(), order)?;
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
    BigInterval::new(low.lo().clone(), high.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)
}

/// `acosh(p) = ln(p + √(p²−1))` for a rational `p >= 1`.
fn acosh_point(p: &BigRational, order: u32) -> Option<BigInterval> {
    if *p < BigRational::one() {
        return None;
    }
    let radicand = p * p - BigRational::one();
    let root = crate::enclosure_special::nth_root_point(&radicand, 2, order)?;
    let argument = root.add(&BigInterval::point(p.clone()));
    let low = crate::enclosure_special::ln_large(argument.lo(), order)?;
    let high = crate::enclosure_special::ln_large(argument.hi(), order)?;
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
    BigInterval::new(low.lo().clone(), high.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)
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
    let probe = enclose_with_reason(base, bindings, precision.min(16))?;
    if !probe.interval.lo().is_positive() {
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
        0..=40 => 32,
        41..=100 => 64,
        _ => 128,
    }
}

/// The dyadic grid the partition and the edge boxes are placed on.
fn quadrature_bits(precision: u32) -> u32 {
    precision.saturating_add(64)
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
        DeclineReason::IntegrandNotEnclosable(format!(
            "on [{}, {}]: {reason}",
            box_.decimal(12),
            box_.decimal(12)
        ))
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
            let value = over.scale(&width);
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
            let fourth = integrand_over(fourth_derivative, var, &span, order)?;
            let simpson = at_lo
                .add(&at_mid.scale(&bi(4)))
                .add(&at_hi)
                .scale(&(&width / bi(6)));
            let error = ratpow_big(&width, 5) * sup_abs(&fourth) / bi(2880);
            let value = BigInterval::new(simpson.lo() - &error, simpson.hi() + &error)
                .ok_or(DeclineReason::PrecisionUnreachable)?;
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
    BigInterval::new(-bound.clone(), bound).ok_or(DeclineReason::PrecisionUnreachable)
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
    let rule = if integrand_over(&fourth_derivative, var, &whole, order).is_ok() {
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
                return Err(format!("panel {index} is inverted"));
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
