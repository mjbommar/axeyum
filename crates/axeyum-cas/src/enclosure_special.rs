//! Certified enclosures for the heads the first slice of
//! [`crate::enclosure`] declined, and for **multivariate** root enclosures by
//! the Krawczyk operator (math-department file 13, Next Ten item **2**, wave
//! two).
//!
//! Everything here obeys the same contract as its parent module: exact
//! `BigRational` endpoints, no `f64` anywhere, a truncation order and an
//! **exact** remainder bound recorded per step, and a verifier that recomputes
//! the bound from `(head, inputs, order)` rather than reading it.
//!
//! # The heads added here
//!
//! | head | method | remainder bound | hypothesis |
//! |---|---|---|---|
//! | `root_q` | Newton `x <- ((q−1)·x + p/x^(q−1))/q` from above | the bracket `[p/x^(q−1), x]` itself | `p >= 0`, `q >= 1`; AM–GM on the `q` terms of the iterate keeps `x >= p^(1/q)`, so the bracket is exact at every step and no error analysis is needed |
//! | `erf`, small | Maclaurin `erf x = (2/√π)·Σ (−1)^k x^(2k+1)/(k!·(2k+1))` | alternating: the tail is at most the first omitted term | the terms must be decreasing from index `n+1`, which holds exactly when `2k² + (5 − 2x²)k + (3 − x²) >= 0`; the module computes the least such `k0` in exact rational arithmetic and declines an order below it |
//! | `erf`, large | the complementary tail `erfc x <= e^(−x²)/(x·√π)` | the bound itself | `x >= 8`; from `erfc x = (2/√π)·∫_x^∞ e^(−t²) dt` and `t/x >= 1` on `[x, ∞)` |
//! | `Gamma`, integer | `Γ(n) = (n−1)!` | none (exact) | `n >= 1` |
//! | `Gamma`, half-integer | `Γ(n + 1/2) = (2n)!/(4^n·n!)·√π` | the `√π` enclosure only | `n >= 0`; the identity is [`crate::special::gamma`]'s, recomputed in `BigInt` because that function is `i128`-bounded |
//! | `Gamma`, general | shift by `Γ(x) = Γ(x+n)/∏_(i<n)(x+i)` to `x+n >= 12+order`, then Stirling `ln Γ z = (z−1/2)·ln z − z + (1/2)·ln 2π + Σ_(k=1)^m B_(2k)/(2k(2k−1)z^(2k−1))` | `|R_m(z)| <= |B_(2m+2)|/((2m+2)(2m+1)·z^(2m+1))` | `z > 0` real: the Stirling series is enveloping there, so the remainder never exceeds the first omitted term and carries its sign (DLMF 5.11.3; Whittaker–Watson §12.33). `x > 0` |
//! | `J_n` | `J_n x = Σ (−1)^k (x/2)^(2k+n)/(k!·(k+n)!)` | alternating: the tail is at most the first omitted term | the terms decrease from the least `k0` with `(k0+1)(k0+n+1) >= (x/2)²`, computed exactly; the module declines an order below it. Over an interval the bound is taken at the endpoint of largest magnitude, where the omitted term is largest |
//!
//! `erf` is odd and increasing, so an interval argument is handled by its two
//! endpoints. `Gamma` and `J_n` are not monotone, so they are evaluated by
//! interval arithmetic over the whole box (`Gamma` through the shift identity,
//! whose two factors *are* monotone on the shifted range); the result is wider
//! than the true image but always contains it.
//!
//! # What it still cannot do
//!
//! - `Gamma` at a **non-positive** argument (the poles and the reflection
//!   region) — declined as a domain error, not continued analytically.
//! - `erf` beyond magnitude `8` to better than the complementary tail bound
//!   allows: that bound is about `2^(−96)` at `x = 8` and improves very fast,
//!   so a request for precision 200 at `x = 8.5` declines rather than lying.
//! - `J_n` of **negative** order, and the second-kind `Y_n`.
//! - A **non-square** or non-polynomial system in [`enclose_system`], any
//!   system whose midpoint Jacobian is singular, and any **multiple** root
//!   (the Krawczyk inclusion test cannot succeed at one — the Jacobian is
//!   singular there, so this is a decline, never a wrong answer).
//!
//! # Multivariate roots
//!
//! [`enclose_system`] refines a box around a root of a square polynomial system
//! with the **Krawczyk operator**
//!
//! ```text
//! K(X) = m − Y·F(m) + (I − Y·J(X))·(X − m),      m = mid X
//! ```
//!
//! where `Y` is the exact rational inverse of the Jacobian at `m`. Two
//! classical facts do all the work, and the verifier re-derives both:
//!
//! 1. **every** zero of `F` in `X` lies in `K(X)`, so `K(X) ∩ X` never drops a
//!    root and the recorded box chain is a chain of valid enclosures;
//! 2. if `K(X) ⊂ int X` then `F` has **exactly one** zero in `X`, and it lies
//!    in `K(X)` (Krawczyk/Moore; the strict inclusion makes `x ↦ x − Y·F(x)` a
//!    contraction of `X` into itself, and Brouwer plus the contraction give
//!    existence and uniqueness).
//!
//! The certificate records the box sequence and, per step, the preconditioner
//! `Y` and the claimed image `K(X)`. [`SystemEnclosure::verify`] recomputes
//! `K(X)` exactly from `(system, domain, Y)` at every step and checks the
//! chain, the strict inclusion at the step that claims existence, and the final
//! width. It never reads the claimed image as an answer.
//!
//! # Cost
//!
//! Wall clock, measured 2026-09-05 under `--release` from the prebuilt test
//! binary, one run each (`cost_table_wave_two`, run with `--nocapture` to
//! re-measure). **ADVISORY ONLY, NOT A BASELINE** — a shared, loaded host and a
//! single unpinned run per row. The current numbers are in the crate-level
//! table in [`crate::enclosure`]; this test is what regenerates them.

use crate::enclosure::{
    BigInterval, DeclineReason, bi, bi_u64, br, exp_point, from_rational, ln_point, pi_enclosure,
    pow2, rat_floor, ratpow, rmax, rmin,
};
use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

/// Above this magnitude `erf` switches from the Maclaurin series to the
/// complementary tail bound: the series stays *sound* for every argument (its
/// coefficients are exact rationals, so there is no cancellation error, only
/// growth), but the order it needs grows like `x²` and the numerators like
/// `x^(2·order)`, and past `8` the tail bound is both cheaper and tighter.
const ERF_SERIES_LIMIT: i64 = 8;

/// The largest number of Stirling correction terms used, so the Bernoulli
/// table stays small and the asymptotic series is truncated well before it
/// starts to diverge.
const STIRLING_TERMS_CAP: u32 = 24;

/// Cap on the shift `Γ(x) = Γ(x+n)/∏(x+i)` and on the search for a
/// monotonicity index, so a pathological argument declines rather than grinds.
const SHIFT_CAP: u32 = 4096;

/// Cap on Krawczyk iterations.
const KRAWCZYK_CAP: u32 = 512;

// ---------------------------------------------------------------------------
// root_q.
// ---------------------------------------------------------------------------

/// The principal `q`-th root of a non-negative rational `p`, as an exact
/// bracket.
///
/// Newton on `f(x) = x^q − p` is `x <- ((q−1)·x + p/x^(q−1))/q`, which is the
/// arithmetic mean of `q−1` copies of `x` and one copy of `p/x^(q−1)`. AM–GM
/// bounds that mean below by the geometric mean
/// `(x^(q−1)·p/x^(q−1))^(1/q) = p^(1/q)`, so **every** iterate is at or above
/// the root whatever the start; and `x >= p^(1/q)` forces
/// `p/x^(q−1) <= p^(1/q)`. So `[p/x^(q−1), x]` brackets the root exactly at
/// every step and the bracket *is* the certificate — the same argument the
/// parent module's `sqrt` uses, generalised from `q = 2`.
///
/// `order` is the iteration cap; the loop also stops once the bracket is
/// narrower than `2^(−2048)`, which keeps the denominators finite and is
/// deterministic in the value rather than in the schedule. Returns `None` for
/// `q = 0` or a negative `p`.
pub(crate) fn nth_root_point(p: &BigRational, q: u32, order: u32) -> Option<BigInterval> {
    if q == 0 || p.is_negative() {
        return None;
    }
    if q == 1 {
        return Some(BigInterval::point(p.clone()));
    }
    if p.is_zero() {
        return Some(BigInterval::point(BigRational::zero()));
    }
    let one = BigRational::one();
    let degree = bi_u64(u64::from(q));
    let below = bi_u64(u64::from(q - 1));
    let mut x = if *p > one { p.clone() } else { one };
    let floor = pow2(-2048);
    for _ in 0..order.max(1) {
        let lower = p / ratpow(&x, q - 1);
        if &x - &lower <= floor {
            break;
        }
        x = (&below * &x + lower) / &degree;
    }
    let lower = p / ratpow(&x, q - 1);
    BigInterval::new(lower, x)
}

// ---------------------------------------------------------------------------
// erf.
// ---------------------------------------------------------------------------

/// The least index from which the Maclaurin terms of `erf` at magnitude `a`
/// are decreasing, or `None` past [`SHIFT_CAP`].
///
/// The terms are `t_k = a^(2k+1)/(k!·(2k+1))`, so
/// `t_(k+1)/t_k = a²(2k+1)/((k+1)(2k+3))`, and the ratio is at most `1` exactly
/// when `2k² + (5 − 2a²)k + (3 − a²) >= 0`. That quadratic in `k` opens upward,
/// so once it holds it holds for every larger `k`; the search below is a scan
/// from `0` in exact rational arithmetic, not a floating-point root formula.
fn erf_monotone_index(a: &BigRational) -> Option<u32> {
    let a2 = a * a;
    for k in 0..SHIFT_CAP {
        let kk = bi_u64(u64::from(k));
        let value = bi(2) * &kk * &kk + (bi(5) - bi(2) * &a2) * &kk + (bi(3) - &a2);
        if !value.is_negative() {
            return Some(k);
        }
    }
    None
}

/// `2/√π` as an interval, from the parent module's Machin enclosure of `pi`.
fn two_over_root_pi(order: u32) -> Option<BigInterval> {
    let pi = pi_enclosure(order)?;
    let root = root_of_interval(&pi, order)?;
    BigInterval::point(bi(2)).div(&root)
}

/// The principal square root of a non-negative interval, endpoint by endpoint.
fn root_of_interval(x: &BigInterval, order: u32) -> Option<BigInterval> {
    if x.lo().is_negative() {
        return None;
    }
    let lo = nth_root_point(x.lo(), 2, order)?;
    let hi = nth_root_point(x.hi(), 2, order)?;
    BigInterval::new(lo.lo().clone(), hi.hi().clone())
}

/// `erf(x)` for a rational `x`, by the alternating Maclaurin series below
/// magnitude [`ERF_SERIES_LIMIT`] and by the complementary tail bound beyond.
///
/// Returns `None` when the requested `order` is below the index from which the
/// series terms decrease (so the alternating bound would not apply) — the
/// caller's order ladder then tries a higher one.
pub(crate) fn erf_point(x: &BigRational, order: u32) -> Option<BigInterval> {
    let a = x.abs();
    let magnitude = if a > bi(ERF_SERIES_LIMIT) {
        erf_tail_bound(&a, order)?
    } else {
        erf_series(&a, order)?
    };
    let one = BigRational::one();
    let clamped = magnitude.clamp(&BigRational::zero(), &one);
    Some(if x.is_negative() {
        clamped.negate()
    } else {
        clamped
    })
}

/// The Maclaurin route, valid because `order` is at or above
/// [`erf_monotone_index`], which is exactly the hypothesis the
/// alternating-series bound needs.
fn erf_series(a: &BigRational, order: u32) -> Option<BigInterval> {
    let start = erf_monotone_index(a)?;
    if order < start {
        return None;
    }
    let a2 = a * a;
    let mut power = a.clone();
    let mut factorial = BigRational::one();
    let mut sum = a.clone();
    let mut sign = -1i64;
    for k in 1..=order {
        power *= &a2;
        factorial *= bi_u64(u64::from(k));
        let denominator = &factorial * bi_u64(2 * u64::from(k) + 1);
        sum += bi(sign) * &power / denominator;
        sign = -sign;
    }
    let next_power = &power * &a2;
    let next_factorial = &factorial * bi_u64(u64::from(order) + 1);
    let remainder = (next_power / (next_factorial * bi_u64(2 * u64::from(order) + 3))).abs();
    let series = BigInterval::center_radius(&sum, &remainder);
    Some(series.mul(&two_over_root_pi(order)?))
}

/// The complementary route: for `a > 0`, `0 < erfc(a) <= e^(−a²)/(a·√π)`, so
/// `erf(a)` lies in `[1 − B, 1]` with `B` an upper bound on that quotient.
///
/// The bound follows from `erfc(a) = (2/√π)·∫_a^∞ e^(−t²) dt` and `t/a >= 1`
/// on the range of integration, which turns the integral into the elementary
/// `∫_a^∞ (t/a)·e^(−t²) dt = e^(−a²)/(2a)`.
fn erf_tail_bound(a: &BigRational, order: u32) -> Option<BigInterval> {
    if !a.is_positive() {
        return None;
    }
    let exponential = exp_point(&-(a * a), order)?;
    let pi = pi_enclosure(order)?;
    let root = root_of_interval(&pi, order)?;
    let bound = exponential.hi() / (a * root.lo());
    let one = BigRational::one();
    BigInterval::new(&one - bound, one)
}

// ---------------------------------------------------------------------------
// Gamma.
// ---------------------------------------------------------------------------

/// The Bernoulli numbers `B_0 .. B_n` as exact `BigRational`s, by
/// `B_m = −(1/(m+1))·Σ_(k<m) C(m+1, k)·B_k`.
///
/// Recomputed in `BigInt` rather than taken from
/// [`crate::combinatorics::bernoulli`], which is `i128`-bounded; that function
/// is the cross-check in `bernoulli_table_matches_the_i128_reference`, not the
/// producer — the same relationship `BigInterval` has to the crate's `i128`
/// interval.
fn bernoulli_table(n: u32) -> Vec<BigRational> {
    let target = n as usize;
    let mut values: Vec<BigRational> = Vec::with_capacity(target + 1);
    for m in 0..=target {
        if m == 0 {
            values.push(BigRational::one());
            continue;
        }
        let upper = m + 1;
        let mut sum = BigRational::zero();
        let mut binomial = BigInt::one();
        for (k, value) in values.iter().enumerate() {
            // C(upper, k) updated in place: C(u, 0) = 1 and
            // C(u, k) = C(u, k−1)·(u − k + 1)/k.
            if k > 0 {
                binomial = binomial * BigInt::from(upper - k + 1) / BigInt::from(k);
            }
            sum += BigRational::from(binomial.clone()) * value;
        }
        values.push(-sum / BigRational::from(BigInt::from(upper)));
    }
    values
}

/// `n!` as a `BigInt`.
fn factorial(n: u64) -> BigInt {
    let mut acc = BigInt::one();
    for i in 2..=n {
        acc *= BigInt::from(i);
    }
    acc
}

/// `Γ` over a positive interval.
///
/// A degenerate interval at a positive integer or half-integer takes the exact
/// closed form; everything else goes through the shift-and-Stirling route,
/// which is evaluated at the two endpoints of the shifted argument (where `Γ`
/// is increasing) and divided by the interval of the shift product (where every
/// factor is positive), so the quotient contains `Γ(x)` for every `x` in the
/// box.
///
/// # Errors
///
/// [`DeclineReason::DomainError`] for an argument reaching `0` or below,
/// [`DeclineReason::ResourceLimit`] when the shift would exceed its cap.
pub(crate) fn gamma_interval(x: &BigInterval, order: u32) -> Result<BigInterval, DeclineReason> {
    if !x.lo().is_positive() {
        return Err(DeclineReason::DomainError(
            "gamma of an interval reaching 0 or below".to_string(),
        ));
    }
    if x.lo() == x.hi()
        && let Some(exact) = gamma_closed_form(x.lo(), order)
    {
        return Ok(exact);
    }
    // The shift target is 12 plus the order, so the Stirling error term
    // |B_(2m+2)|/((2m+2)(2m+1)·z^(2m+1)) keeps shrinking as the ladder climbs
    // even once the Bernoulli count is capped.
    let target = bi_u64(12 + u64::from(order));
    let shift = shift_count(x.lo(), &target)?;
    let mut product = BigInterval::point(BigRational::one());
    for i in 0..shift {
        let step = BigInterval::new(x.lo() + bi_u64(u64::from(i)), x.hi() + bi_u64(u64::from(i)))
            .ok_or(DeclineReason::ResourceLimit)?;
        product = product.mul(&step);
    }
    let shifted_lo = x.lo() + bi_u64(u64::from(shift));
    let shifted_hi = x.hi() + bi_u64(u64::from(shift));
    let low = gamma_stirling_point(&shifted_lo, order).ok_or(DeclineReason::ResourceLimit)?;
    let high = gamma_stirling_point(&shifted_hi, order).ok_or(DeclineReason::ResourceLimit)?;
    // Γ is increasing on [2, ∞), and the shift target is well above 2.
    let numerator = BigInterval::new(low.lo().clone(), high.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    numerator
        .div(&product)
        .ok_or(DeclineReason::DivisorContainsZero)
}

/// How many unit shifts take `x` to at least `target`, or a resource decline.
fn shift_count(x: &BigRational, target: &BigRational) -> Result<u32, DeclineReason> {
    if x >= target {
        return Ok(0);
    }
    let needed = rat_floor(&(target - x)) + BigInt::one();
    u32::try_from(needed)
        .ok()
        .filter(|n| *n <= SHIFT_CAP)
        .ok_or(DeclineReason::ResourceLimit)
}

/// `Γ` at a positive integer or half-integer, exactly.
///
/// `Γ(n) = (n−1)!`, and `Γ(n + 1/2) = (2n)!/(4^n·n!)·√π` — the identity
/// [`crate::special::gamma`] uses, recomputed in `BigInt` so it does not stop
/// at the `i128` range. Returns `None` for any other rational.
fn gamma_closed_form(x: &BigRational, order: u32) -> Option<BigInterval> {
    if !x.is_positive() {
        return None;
    }
    let denominator = x.denom();
    let numerator = x.numer();
    if denominator.is_one() {
        let n = u64::try_from(numerator.clone()).ok()?;
        if n < 1 {
            return None;
        }
        return Some(BigInterval::point(BigRational::from(factorial(n - 1))));
    }
    if *denominator == BigInt::from(2u32) {
        let m = u64::try_from(numerator.clone()).ok()?;
        if m < 1 {
            return None;
        }
        let n = (m - 1) / 2;
        let coefficient = BigRational::new(
            factorial(2 * n),
            BigInt::from(4u32).pow(u32::try_from(n).ok()?) * factorial(n),
        );
        let pi = pi_enclosure(order)?;
        let root = root_of_interval(&pi, order)?;
        return Some(root.scale(&coefficient));
    }
    None
}

/// `Γ(y)` for a rational `y` at or above the Stirling shift target, by
/// `exp(ln Γ y)`.
///
/// `ln Γ z = (z − 1/2)·ln z − z + (1/2)·ln 2π + Σ_(k=1)^m B_(2k)/(2k(2k−1)·z^(2k−1))`
/// with the classical remainder bound
/// `|R_m(z)| <= |B_(2m+2)|/((2m+2)(2m+1)·z^(2m+1))` for real `z > 0` — the
/// Stirling series is enveloping there, so the remainder never exceeds the
/// first omitted term (DLMF 5.11.3; Whittaker–Watson §12.33).
fn gamma_stirling_point(y: &BigRational, order: u32) -> Option<BigInterval> {
    if !y.is_positive() {
        return None;
    }
    let terms = order.clamp(1, STIRLING_TERMS_CAP);
    let bernoulli = bernoulli_table(2 * terms + 2);
    let half = br(1, 2);
    let ln_y = ln_point(y, order)?;
    let pi = pi_enclosure(order)?;
    let two_pi = pi.scale(&bi(2));
    let ln_two_pi_lo = ln_point(two_pi.lo(), order)?;
    let ln_two_pi_hi = ln_point(two_pi.hi(), order)?;
    let ln_two_pi = BigInterval::new(ln_two_pi_lo.lo().clone(), ln_two_pi_hi.hi().clone())?;
    let mut total = ln_y
        .scale(&(y - &half))
        .sub(&BigInterval::point(y.clone()))
        .add(&ln_two_pi.scale(&half));
    for k in 1..=terms {
        let index = 2 * u64::from(k);
        let coefficient = &bernoulli[index as usize]
            / (bi_u64(index) * bi_u64(index - 1) * ratpow(y, 2 * k - 1));
        total = total.add(&BigInterval::point(coefficient));
    }
    let next = 2 * u64::from(terms) + 2;
    let error = (&bernoulli[next as usize]
        / (bi_u64(next) * bi_u64(next - 1) * ratpow(y, 2 * terms + 1)))
        .abs();
    let bounded = BigInterval::new(total.lo() - &error, total.hi() + &error)?;
    let low = exp_point(bounded.lo(), order)?;
    let high = exp_point(bounded.hi(), order)?;
    BigInterval::new(low.lo().clone(), high.hi().clone())
}

// ---------------------------------------------------------------------------
// Bessel J_n.
// ---------------------------------------------------------------------------

/// The least index from which the `J_n` series terms at magnitude `a` are
/// decreasing: `t_(k+1)/t_k = (a/2)²/((k+1)(k+n+1))`, so the terms fall once
/// `(k+1)(k+n+1) >= (a/2)²`. Exact rational scan; `None` past [`SHIFT_CAP`].
fn bessel_monotone_index(a: &BigRational, n: u32) -> Option<u32> {
    let quarter = (a * a) / bi(4);
    for k in 0..SHIFT_CAP {
        let left = bi_u64(u64::from(k) + 1) * bi_u64(u64::from(k) + u64::from(n) + 1);
        if left >= quarter {
            return Some(k);
        }
    }
    None
}

/// `J_n` over an interval by its power series, evaluated with interval
/// arithmetic and closed with the alternating tail bound taken at the endpoint
/// of largest magnitude, where every omitted term is largest.
///
/// Returns `None` when `order` is below [`bessel_monotone_index`], so the
/// alternating bound would not apply.
pub(crate) fn bessel_j_interval(n: u32, x: &BigInterval, order: u32) -> Option<BigInterval> {
    let a = rmax(x.lo().abs(), x.hi().abs());
    let start = bessel_monotone_index(&a, n)?;
    if order < start {
        return None;
    }
    let half = x.scale(&br(1, 2));
    let mut sum = BigInterval::point(BigRational::zero());
    let mut shifted_factorial = BigRational::from(factorial(u64::from(n)));
    let mut k_factorial = BigRational::one();
    let mut sign = 1i64;
    for k in 0..=order {
        if k > 0 {
            k_factorial *= bi_u64(u64::from(k));
            shifted_factorial *= bi_u64(u64::from(k) + u64::from(n));
        }
        let exponent = 2 * k + n;
        let coefficient = bi(sign) / (&k_factorial * &shifted_factorial);
        sum = sum.add(&half.pow(exponent).scale(&coefficient));
        sign = -sign;
    }
    let next = order + 1;
    let next_k = &k_factorial * bi_u64(u64::from(next));
    let next_shifted = &shifted_factorial * bi_u64(u64::from(next) + u64::from(n));
    let remainder = ratpow(&(a / bi(2)), 2 * next + n) / (next_k * next_shifted);
    let one = BigRational::one();
    // |J_n(x)| <= 1 for every real x and every integer n >= 0.
    Some(BigInterval::new(sum.lo() - &remainder, sum.hi() + &remainder)?.clamp(&-one.clone(), &one))
}

// ---------------------------------------------------------------------------
// Multivariate polynomial systems.
// ---------------------------------------------------------------------------

/// A multivariate polynomial with exact rational coefficients over a fixed
/// number of variables.
///
/// Terms are keyed by their exponent vector in a [`BTreeMap`], so iteration is
/// the deterministic lexicographic order of the exponents and never a hash
/// order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiPoly {
    dimension: usize,
    terms: BTreeMap<Vec<u32>, BigRational>,
}

impl MultiPoly {
    /// The zero polynomial in `dimension` variables.
    #[must_use]
    pub fn zero(dimension: usize) -> MultiPoly {
        MultiPoly {
            dimension,
            terms: BTreeMap::new(),
        }
    }

    /// Add `coefficient · x_0^e_0 · … · x_(d−1)^e_(d−1)`, or `None` when the
    /// exponent vector has the wrong length. A term that cancels to zero is
    /// dropped, so two polynomials equal as functions compare equal.
    #[must_use]
    pub fn with_term(mut self, coefficient: Rational, exponents: &[u32]) -> Option<MultiPoly> {
        if exponents.len() != self.dimension {
            return None;
        }
        let value = from_rational(coefficient);
        let slot = self
            .terms
            .entry(exponents.to_vec())
            .or_insert_with(BigRational::zero);
        *slot += value;
        if slot.is_zero() {
            self.terms.remove(exponents);
        }
        Some(self)
    }

    /// The number of variables.
    #[must_use]
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// The value over a box, by interval arithmetic term by term.
    fn eval_interval(&self, region: &[BigInterval]) -> BigInterval {
        let mut total = BigInterval::point(BigRational::zero());
        for (exponents, coefficient) in &self.terms {
            let mut term = BigInterval::point(coefficient.clone());
            for (slot, exponent) in exponents.iter().enumerate() {
                term = term.mul(&region[slot].pow(*exponent));
            }
            total = total.add(&term);
        }
        total
    }

    /// The value at an exact rational point.
    fn eval_point(&self, point: &[BigRational]) -> BigRational {
        let mut total = BigRational::zero();
        for (exponents, coefficient) in &self.terms {
            let mut term = coefficient.clone();
            for (slot, exponent) in exponents.iter().enumerate() {
                term *= ratpow(&point[slot], *exponent);
            }
            total += term;
        }
        total
    }

    /// The exact partial derivative with respect to variable `slot`.
    fn derivative(&self, slot: usize) -> MultiPoly {
        let mut out = MultiPoly::zero(self.dimension);
        for (exponents, coefficient) in &self.terms {
            let exponent = exponents[slot];
            if exponent == 0 {
                continue;
            }
            let mut lowered = exponents.clone();
            lowered[slot] = exponent - 1;
            let scaled = coefficient * bi_u64(u64::from(exponent));
            let entry = out.terms.entry(lowered).or_insert_with(BigRational::zero);
            *entry += scaled;
        }
        out.terms.retain(|_, value| !value.is_zero());
        out
    }
}

/// A **square** system of multivariate polynomials: `n` equations in `n`
/// variables, all with exact rational coefficients.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolySystem {
    dimension: usize,
    equations: Vec<MultiPoly>,
    jacobian: Vec<Vec<MultiPoly>>,
}

impl PolySystem {
    /// The system of the given equations, or `None` when it is not square or
    /// the equations disagree about the number of variables.
    #[must_use]
    pub fn new(equations: Vec<MultiPoly>) -> Option<PolySystem> {
        let dimension = equations.len();
        if dimension == 0 || equations.iter().any(|e| e.dimension() != dimension) {
            return None;
        }
        let jacobian = equations
            .iter()
            .map(|equation| {
                (0..dimension)
                    .map(|slot| equation.derivative(slot))
                    .collect()
            })
            .collect();
        Some(PolySystem {
            dimension,
            equations,
            jacobian,
        })
    }

    /// The number of variables (equivalently, of equations).
    #[must_use]
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// `F(x)` at an exact rational point.
    fn value_at(&self, point: &[BigRational]) -> Vec<BigRational> {
        self.equations.iter().map(|e| e.eval_point(point)).collect()
    }

    /// The Jacobian at an exact rational point.
    fn jacobian_at(&self, point: &[BigRational]) -> Vec<Vec<BigRational>> {
        self.jacobian
            .iter()
            .map(|row| row.iter().map(|e| e.eval_point(point)).collect())
            .collect()
    }

    /// The Jacobian over a box, entry by entry.
    fn jacobian_over(&self, region: &[BigInterval]) -> Vec<Vec<BigInterval>> {
        self.jacobian
            .iter()
            .map(|row| row.iter().map(|e| e.eval_interval(region)).collect())
            .collect()
    }
}

/// The exact inverse of a square rational matrix by Gauss–Jordan with the
/// first-nonzero pivot, or `None` when it is singular.
///
/// Exact `BigRational` throughout. The crate's `matrix::Matrix` is
/// `CasExpr`/`i128`-backed, and a midpoint after a dozen Krawczyk steps has a
/// denominator near `2^precision`, so inverting through it would overflow
/// inside a certified path — the same reason `BigInterval` exists beside the
/// crate's `i128` interval.
fn invert(matrix: &[Vec<BigRational>]) -> Option<Vec<Vec<BigRational>>> {
    let n = matrix.len();
    if matrix.iter().any(|row| row.len() != n) {
        return None;
    }
    let mut work: Vec<Vec<BigRational>> = matrix
        .iter()
        .enumerate()
        .map(|(row, entries)| {
            let mut extended = entries.clone();
            for column in 0..n {
                extended.push(if column == row {
                    BigRational::one()
                } else {
                    BigRational::zero()
                });
            }
            extended
        })
        .collect();
    for column in 0..n {
        let pivot = (column..n).find(|row| !work[*row][column].is_zero())?;
        work.swap(column, pivot);
        let scale = work[column][column].clone();
        for entry in &mut work[column] {
            *entry /= &scale;
        }
        for row in 0..n {
            if row == column {
                continue;
            }
            let factor = work[row][column].clone();
            if factor.is_zero() {
                continue;
            }
            for index in 0..2 * n {
                let subtrahend = &work[column][index] * &factor;
                work[row][index] -= subtrahend;
            }
        }
    }
    Some(work.into_iter().map(|row| row[n..].to_vec()).collect())
}

/// One Krawczyk step: the box it acted on, the preconditioner it used, the
/// image it claims, whether that image was strictly inside the box, and the
/// box it produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KrawczykStep {
    /// The box `X` the operator was applied to.
    pub domain: Vec<BigInterval>,
    /// The rational matrix `Y` used to precondition — the exact inverse of the
    /// Jacobian at the midpoint of `domain`. Soundness does not depend on `Y`
    /// being that particular matrix; the contraction does.
    pub preconditioner: Vec<Vec<BigRational>>,
    /// The claimed `K(X)`. The verifier recomputes it and never reads this as
    /// an answer.
    pub image: Vec<BigInterval>,
    /// Whether `K(X)` was strictly inside `X` in every coordinate — the
    /// inclusion that proves existence and uniqueness.
    pub strict: bool,
    /// The box carried forward, which must contain `K(X) ∩ X`.
    pub output: Vec<BigInterval>,
}

/// A box enclosing a simple root of a square polynomial system, with the
/// Krawczyk evidence that produced it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SystemEnclosure {
    /// The final box. Every coordinate has width at most `2^(−precision)`.
    pub region: Vec<BigInterval>,
    /// The requested precision.
    pub precision: u32,
    /// The Krawczyk steps, in order.
    pub steps: Vec<KrawczykStep>,
    /// The index of the step whose strict inclusion proves that the system has
    /// **exactly one** root in that step's domain.
    pub existence_step: usize,
}

/// The Krawczyk image `K(X) = m − Y·F(m) + (I − Y·J(X))·(X − m)`.
///
/// Deterministic in `(system, region, preconditioner)` alone, which is what
/// lets the verifier recompute it from the certificate.
fn krawczyk_image(
    system: &PolySystem,
    region: &[BigInterval],
    preconditioner: &[Vec<BigRational>],
) -> Option<Vec<BigInterval>> {
    let n = system.dimension();
    if region.len() != n || preconditioner.len() != n {
        return None;
    }
    if preconditioner.iter().any(|row| row.len() != n) {
        return None;
    }
    let midpoint: Vec<BigRational> = region.iter().map(BigInterval::midpoint).collect();
    let value = system.value_at(&midpoint);
    let jacobian = system.jacobian_over(region);
    let offset: Vec<BigInterval> = region
        .iter()
        .zip(&midpoint)
        .map(|(interval, centre)| {
            BigInterval::new(interval.lo() - centre, interval.hi() - centre)
                .unwrap_or_else(|| BigInterval::point(BigRational::zero()))
        })
        .collect();
    let mut image = Vec::with_capacity(n);
    for row in 0..n {
        // m_row − (Y·F(m))_row.
        let mut centre = midpoint[row].clone();
        for (column, entry) in value.iter().enumerate() {
            centre -= &preconditioner[row][column] * entry;
        }
        let mut accumulated = BigInterval::point(centre);
        for column in 0..n {
            // (I − Y·J(X))_(row, column).
            let mut entry = BigInterval::point(if row == column {
                BigRational::one()
            } else {
                BigRational::zero()
            });
            for index in 0..n {
                entry = entry.sub(&jacobian[index][column].scale(&preconditioner[row][index]));
            }
            accumulated = accumulated.add(&entry.mul(&offset[column]));
        }
        image.push(accumulated);
    }
    Some(image)
}

/// Whether `image` lies strictly inside `region` in every coordinate.
fn strictly_inside(image: &[BigInterval], region: &[BigInterval]) -> bool {
    image.len() == region.len()
        && image
            .iter()
            .zip(region)
            .all(|(inner, outer)| outer.lo() < inner.lo() && inner.hi() < outer.hi())
}

/// The coordinatewise intersection, or `None` when any coordinate is empty.
fn intersect(a: &[BigInterval], b: &[BigInterval]) -> Option<Vec<BigInterval>> {
    if a.len() != b.len() {
        return None;
    }
    a.iter()
        .zip(b)
        .map(|(x, y)| {
            BigInterval::new(
                rmax(x.lo().clone(), y.lo().clone()),
                rmin(x.hi().clone(), y.hi().clone()),
            )
        })
        .collect()
}

/// Refine a starting box to a certified enclosure of a **simple** root of a
/// square rational polynomial system, by the Krawczyk operator.
///
/// Returns `None` when no certificate was produced; use
/// [`enclose_system_with_reason`] for the obstacle.
#[must_use]
pub fn enclose_system(
    system: &PolySystem,
    start: &[BigInterval],
    precision: u32,
) -> Option<SystemEnclosure> {
    enclose_system_with_reason(system, start, precision).ok()
}

/// [`enclose_system`], reporting the obstacle when it declines.
///
/// # Errors
///
/// - [`DeclineReason::NotIsolating`] when the operator never contracts strictly
///   into the box (no root is proved to exist there), or when the intersection
///   `K(X) ∩ X` is empty, which **proves** the box holds no root;
/// - [`DeclineReason::DomainError`] when the Jacobian at a midpoint is
///   singular, or the starting box has the wrong length;
/// - [`DeclineReason::PrecisionUnreachable`] when the iteration stops making
///   progress before the width bound, and [`DeclineReason::ResourceLimit`]
///   when it exceeds the iteration cap.
pub fn enclose_system_with_reason(
    system: &PolySystem,
    start: &[BigInterval],
    precision: u32,
) -> Result<SystemEnclosure, DeclineReason> {
    let n = system.dimension();
    if start.len() != n {
        return Err(DeclineReason::DomainError(
            "the starting box does not have one interval per variable".to_string(),
        ));
    }
    let target = pow2(-i32::try_from(precision.min(1_000_000)).unwrap_or(i32::MAX));
    let mut region: Vec<BigInterval> = start.to_vec();
    let mut steps: Vec<KrawczykStep> = Vec::new();
    let mut existence: Option<usize> = None;
    for _ in 0..KRAWCZYK_CAP {
        let midpoint: Vec<BigRational> = region.iter().map(BigInterval::midpoint).collect();
        let preconditioner = invert(&system.jacobian_at(&midpoint)).ok_or_else(|| {
            DeclineReason::DomainError("the Jacobian at the midpoint is singular".to_string())
        })?;
        let image = krawczyk_image(system, &region, &preconditioner)
            .ok_or(DeclineReason::PrecisionUnreachable)?;
        let strict = strictly_inside(&image, &region);
        let next = intersect(&image, &region).ok_or(DeclineReason::NotIsolating)?;
        if strict && existence.is_none() {
            existence = Some(steps.len());
        }
        let progressed = next != region;
        steps.push(KrawczykStep {
            domain: region.clone(),
            preconditioner,
            image,
            strict,
            output: next.clone(),
        });
        region = next;
        let widest = region
            .iter()
            .map(BigInterval::width)
            .fold(BigRational::zero(), rmax);
        if let Some(existence_step) = existence
            && widest <= target
        {
            return Ok(SystemEnclosure {
                region,
                precision,
                steps,
                existence_step,
            });
        }
        if !progressed {
            return Err(if existence.is_some() {
                DeclineReason::PrecisionUnreachable
            } else {
                DeclineReason::NotIsolating
            });
        }
    }
    Err(DeclineReason::ResourceLimit)
}

impl SystemEnclosure {
    /// Re-derive the whole Krawczyk chain and refuse anything that does not
    /// hold up.
    ///
    /// The verifier recomputes `K(X)` from `(system, domain, preconditioner)`
    /// at every step; it reads the recorded `image` and `strict` only as claims
    /// to be checked. The guards, each with a test that dies when the guard is
    /// deleted:
    ///
    /// 1. **shape** — at least one step, every box one interval per variable,
    ///    every preconditioner square of that size;
    /// 2. **start** — the first step's domain must be the box the caller
    ///    started from;
    /// 3. **chain** — each step's domain must be the previous step's output;
    /// 4. **image understated** — the recomputed `K(X)` must lie inside the
    ///    recorded image, so a forger cannot claim a smaller operator value;
    /// 5. **contraction** — the recorded output must contain `K(X) ∩ X`, so no
    ///    root of the system in `X` is dropped from the chain;
    /// 6. **existence** — at the recorded existence step the **recomputed**
    ///    `K(X)` must lie strictly inside that step's domain, which is what
    ///    proves the system has exactly one root there;
    /// 7. **final box** — the enclosure must be the last step's output;
    /// 8. **width** — every coordinate's width must be at most
    ///    `2^(−precision)`.
    ///
    /// # Errors
    ///
    /// Returns a message naming the guard that fired and the step it fired on.
    pub fn verify(&self, system: &PolySystem, start: &[BigInterval]) -> Result<(), String> {
        let n = system.dimension();
        // Guard 1: shape.
        if self.steps.is_empty() {
            return Err("a system certificate carries at least one Krawczyk step".into());
        }
        for (index, step) in self.steps.iter().enumerate() {
            if step.domain.len() != n || step.output.len() != n || step.image.len() != n {
                return Err(format!(
                    "step {index} has a box of the wrong dimension for a system in {n} variables"
                ));
            }
            if step.preconditioner.len() != n || step.preconditioner.iter().any(|r| r.len() != n) {
                return Err(format!(
                    "step {index} has a preconditioner that is not {n} by {n}"
                ));
            }
        }
        // Guard 2: the chain starts where the caller said.
        if self.steps[0].domain != start {
            return Err("the first step does not start from the given box".into());
        }
        if self.existence_step >= self.steps.len() {
            return Err("the existence step is out of range".into());
        }
        for (index, step) in self.steps.iter().enumerate() {
            // Guard 3: the chain is linked.
            if index > 0 && step.domain != self.steps[index - 1].output {
                return Err(format!(
                    "step {index} does not start from the box step {} produced",
                    index - 1
                ));
            }
            let recomputed = krawczyk_image(system, &step.domain, &step.preconditioner)
                .ok_or_else(|| format!("step {index} does not re-evaluate"))?;
            // Guard 4: image understated.
            for (slot, (claimed, actual)) in step.image.iter().zip(&recomputed).enumerate() {
                if !claimed.contains_interval(actual) {
                    return Err(format!(
                        "step {index} claims a Krawczyk image whose coordinate {slot} does not contain the recomputed one"
                    ));
                }
            }
            // Guard 5: the contraction keeps every root.
            let kept = intersect(&recomputed, &step.domain)
                .ok_or_else(|| format!("step {index} has an empty intersection"))?;
            for (slot, (output, needed)) in step.output.iter().zip(&kept).enumerate() {
                if !output.contains_interval(needed) {
                    return Err(format!(
                        "step {index} drops part of the Krawczyk image at coordinate {slot}"
                    ));
                }
            }
            // Guard 6: the existence claim, recomputed.
            if index == self.existence_step {
                if !step.strict {
                    return Err(format!(
                        "step {index} is named as the existence step but claims no strict inclusion"
                    ));
                }
                if !strictly_inside(&recomputed, &step.domain) {
                    return Err(format!(
                        "step {index} claims a strict inclusion the recomputed operator does not satisfy"
                    ));
                }
            }
        }
        // Guard 7: the final box is the chain's last output.
        let last = &self.steps[self.steps.len() - 1].output;
        if self.region != *last {
            return Err("the enclosure is not the box the last step produced".into());
        }
        // Guard 8: width.
        let target = pow2(-i32::try_from(self.precision.min(1_000_000)).unwrap_or(i32::MAX));
        for (slot, interval) in self.region.iter().enumerate() {
            if interval.width() > target {
                return Err(format!(
                    "coordinate {slot} has width {} which exceeds 2^-{}",
                    interval.width(),
                    self.precision
                ));
            }
        }
        Ok(())
    }
}

/// A box of rational endpoints, for [`enclose_system`].
///
/// ```
/// use axeyum_cas::enclosure_special::rational_box;
/// use axeyum_ir::Rational;
/// let region = rational_box(&[(Rational::integer(0), Rational::integer(1))]).unwrap();
/// assert_eq!(region.len(), 1);
/// ```
#[must_use]
pub fn rational_box(bounds: &[(Rational, Rational)]) -> Option<Vec<BigInterval>> {
    bounds
        .iter()
        .map(|(lo, hi)| BigInterval::new(from_rational(*lo), from_rational(*hi)))
        .collect()
}
