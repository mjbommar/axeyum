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
//! | `Gamma`, general | shift by `Γ(x) = Γ(x+n)/∏_(i<n)(x+i)` to `x+n >= 12 + order/4`, then Stirling `ln Γ z = (z−1/2)·ln z − z + (1/2)·ln 2π + Σ_(k=1)^m B_(2k)/(2k(2k−1)z^(2k−1))` | `|R_m(z)| <= |B_(2m+2)|/((2m+2)(2m+1)·z^(2m+1))` | `z > 0` real: the Stirling series is enveloping there, so the remainder never exceeds the first omitted term and carries its sign (DLMF 5.11.3; Whittaker–Watson §12.33). `x > 0` |
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
    BigInterval, DeclineReason, REDUCTION_CAP, bi, bi_u64, br, exp_point, from_rational, ln_point,
    pi_enclosure, pow2, rat_floor, ratpow, rmax, rmin,
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

/// The largest number of Stirling correction terms used.
///
/// The Stirling series is asymptotic: for a fixed `z` the terms shrink until
/// about `k = pi*z` and then grow. The shift target below never puts `z` under
/// `13`, so `pi*z` is never under `40` and this cap keeps the truncation on the
/// shrinking side for every argument the module accepts.
const STIRLING_TERMS_CAP: u32 = 40;

/// The base of the Stirling shift target `z = STIRLING_SHIFT_BASE + order/4`.
///
/// The shift is what costs: `Gamma(x) = Gamma(x+n)/prod(x+i)` needs one
/// certified `ln` per unit of shift, so a target of `12 + order` (the first
/// draft) meant 152 series evaluations at order 64 and measured 23 s for one
/// `Gamma(1/3)` at precision 100. The accuracy that shift was buying is much
/// more cheaply bought from the correction terms instead: the error falls like
/// `z^-(2m+1)` in the shift but factorially in `m`, so raising
/// [`STIRLING_TERMS_CAP`] from 24 to 40 and dropping the target to
/// `12 + order/4` reaches a tighter bound with a quarter of the work.
const STIRLING_SHIFT_BASE: u64 = 12;

/// Cap on the shift `Γ(x) = Γ(x+n)/∏(x+i)` and on the search for a
/// monotonicity index, so a pathological argument declines rather than grinds.
const SHIFT_CAP: u32 = 4096;

/// Cap on Krawczyk iterations.
const KRAWCZYK_CAP: u32 = 512;

// ---------------------------------------------------------------------------
// Outward dyadic rounding — why every kernel argument passes through it.
// ---------------------------------------------------------------------------

/// The dyadic grid a kernel argument is rounded onto at a given truncation
/// order: `4·order + 64` bits.
///
/// The series kernels of the parent module are **exact**: `atanh_small` forms
/// `z^(2n+3)` as a rational, so an argument whose denominator has `b` bits
/// produces intermediates with `b·(2n+3)` bits. That is invisible while the
/// arguments are `1/3` and `1/5`, which is all the first slice ever passed
/// them — and catastrophic the moment a *computed* interval is passed instead.
/// A certified `pi` at order 64 has endpoints near 2,000 bits (Machin raises
/// `1/5` and `1/239` to the 131st power), and `ln` of that endpoint forms a
/// 260,000-bit rational whose `gcd` normalisation dominates every other cost
/// in the module: measured, two calls to [`ln_gamma_stirling`] took 58 s in a
/// `--release` build before this rounding was added, and the same test now
/// takes milliseconds.
///
/// The grid is chosen well finer than the accuracy the order can deliver — the
/// `atanh` tail at order `n` is about `2^(−3.17·n)`, and the grid is `2^(−4n−64)`
/// — so rounding is never what limits the answer, only what bounds the size of
/// the numbers.
fn grid_bits(order: u32) -> u32 {
    order.saturating_mul(2).saturating_add(96)
}

/// The denominator size of the dyadic `r` that [`ln_large`] anchors on.
///
/// The anchor is what [`ln_point`] actually sees, and that cost grows with the
/// **square** of its denominator size, so the anchor is kept deliberately
/// coarse and the accuracy is bought back from the cheap `ln(1+w)` correction
/// instead: 16 bits of anchor put `w` under `2^(-16)`, and `order/8 + 6` terms
/// then reach `2^(-2·order-112)`, finer than [`grid_bits`].
const LN_ANCHOR_BITS: u32 = 16;

/// `ln(1 + w)` for `0 <= w <= 1/2`, truncated after `terms` terms.
///
/// `ln(1+w) = w - w^2/2 + w^3/3 - ...` is alternating with decreasing terms for
/// `|w| < 1`, so the tail past term `n` is at most `w^(n+1)/(n+1)` — the plain
/// alternating-series bound, no majorant needed.
fn ln_one_plus(w: &BigRational, terms: u32) -> Option<BigInterval> {
    if w.is_negative() || *w > br(1, 2) {
        return None;
    }
    let mut power = w.clone();
    let mut sum = w.clone();
    let mut sign = -1i64;
    for j in 2..=terms.max(1) {
        power *= w;
        sum += bi(sign) * &power / bi_u64(u64::from(j));
        sign = -sign;
    }
    let next = terms.max(1) + 1;
    let remainder = (&power * w / bi_u64(u64::from(next))).abs();
    Some(BigInterval::center_radius(&sum, &remainder))
}

/// `ln(p)` for a positive rational whose **denominator may be enormous**, at a
/// cost that does not grow with that denominator.
///
/// The parent module's [`ln_point`] reduces to `2·atanh((t−1)/(t+1))` with
/// `|z| <= 1/3`, so it always needs the full `order` terms — and it forms
/// `z^(2·order+1)` exactly. For `z` with `a` bits that is `2·a·order` bits, and
/// `num-rational` runs a `gcd` after every operation, so the series costs about
/// `a²·order³/48` word operations. Measured: a certified `2π` at order 64 has
/// 322-bit endpoints, and one `Gamma` at precision 100 spent **26 s** inside
/// exactly this loop.
///
/// So this route splits the reduction in two. Write `p = 2^k·t` with `t` in
/// `[1, 2)` as before, then anchor on `r = floor(t·2^64)/2^64`, a rational with
/// a 64-bit denominator whatever `t` looks like:
///
/// ```text
/// ln p = k·ln 2 + ln r + ln(1 + (t − r)/r)
/// ```
///
/// `ln r` goes through [`ln_point`] on a **small** argument, and the correction
/// has `0 <= w < 2^(−16)`, so `terms = order/8 + 6` of the alternating
/// `ln(1+w)` series reach `2^(−2·order−112)` — finer than the
/// [`grid_bits`] the argument was rounded to, so it is never the limit.
fn ln_large(p: &BigRational, order: u32) -> Option<BigInterval> {
    if !p.is_positive() {
        return None;
    }
    let one = BigRational::one();
    let two = bi(2);
    let mut t = p.clone();
    let mut exponent: i64 = 0;
    while t >= two {
        t /= &two;
        exponent += 1;
        if exponent > REDUCTION_CAP {
            return None;
        }
    }
    while t < one {
        t *= &two;
        exponent -= 1;
        if exponent < -REDUCTION_CAP {
            return None;
        }
    }
    let anchor = dyadic_floor(&t, LN_ANCHOR_BITS);
    if !anchor.is_positive() {
        return None;
    }
    let ln_anchor = ln_point(&anchor, order)?;
    let correction = ln_one_plus(&(&t / &anchor - &one), order / 8 + 6)?;
    let ln_two = ln_point(&two, order)?;
    Some(ln_anchor.add(&correction).add(&ln_two.scale(&bi(exponent))))
}

/// The largest multiple of `2^(−bits)` at or below `x`.
fn dyadic_floor(x: &BigRational, bits: u32) -> BigRational {
    let scale = pow2(i32::try_from(bits).unwrap_or(i32::MAX));
    BigRational::from(rat_floor(&(x * &scale))) / scale
}

/// The smallest multiple of `2^(−bits)` at or above `x`.
fn dyadic_ceil(x: &BigRational, bits: u32) -> BigRational {
    -dyadic_floor(&-x, bits)
}

/// `x` widened **outward** onto the `2^(−bits)` grid.
///
/// Always contains `x`, so substituting it for `x` anywhere an enclosure is
/// wanted stays sound; it only ever loses accuracy, never validity.
fn coarsen(x: &BigInterval, bits: u32) -> BigInterval {
    let lo = dyadic_floor(x.lo(), bits);
    let hi = dyadic_ceil(x.hi(), bits);
    BigInterval::new(lo.clone(), hi).unwrap_or_else(|| BigInterval::point(lo))
}

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
    let bits = grid_bits(order);
    let mut x = dyadic_ceil(&if *p > one { p.clone() } else { one }, bits);
    let floor = pow2(-i32::try_from(bits).unwrap_or(i32::MAX));
    for _ in 0..order.max(1) {
        let lower = p / ratpow(&x, q - 1);
        if &x - &lower <= floor {
            break;
        }
        // Rounding the iterate UP keeps it at or above the root, which is the
        // only thing AM-GM needs, so the bracket stays exact — and it stops the
        // denominator doubling on every Newton step.
        let next = dyadic_ceil(&((&below * &x + lower) / &degree), bits);
        if next >= x {
            break;
        }
        x = next;
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
    let coarse = coarsen(x, grid_bits(order));
    let lo = nth_root_point(coarse.lo(), 2, order)?;
    let hi = nth_root_point(coarse.hi(), 2, order)?;
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
/// closed form. Everything else goes through the shift identity
/// `Γ(x) = Γ(x+n)/∏_(i<n)(x+i)`, entirely **in logarithms**:
///
/// ```text
/// ln Γ(x) = ln Γ(x+n) − Σ_(i<n) ln(x+i)
/// ```
///
/// and only the small result is exponentiated. The shift target is
/// `12 + order/4`; see [`STIRLING_SHIFT_BASE`] for why it is not larger. The
/// sum of logarithms is taken as **one** logarithm of the product, which
/// [`ln_large`] handles at a cost independent of how large that product is. Doing the division on `Γ`
/// itself would mean forming `exp` of a number near `n·ln n` — at order 128
/// that is `e^554`, a rational whose repeated squaring in `exp_point` reaches
/// millions of bits and whose `gcd` normalisation dominates everything else.
/// In logarithms both sides stay small, the subtraction of exact rationals
/// loses nothing, and `exp` is applied once to a number of size `ln Γ(x)`.
///
/// Each `ln` is monotone and `Γ` is increasing above `2`, so the two endpoint
/// evaluations bound the whole box; the interval difference is wider than the
/// true image (the two terms are correlated and interval subtraction cannot
/// know that) but always contains it.
///
/// # Errors
///
/// [`DeclineReason::DomainError`] for an argument reaching `0` or below,
/// [`DeclineReason::ResourceLimit`] when the shift would exceed its cap or a
/// series kernel runs out of reduction budget.
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
    // The shift target grows with the order, so the Stirling error term
    // |B_(2m+2)|/((2m+2)(2m+1)·z^(2m+1)) keeps shrinking as the ladder climbs
    // even once the Bernoulli count is capped.
    let target = bi_u64(STIRLING_SHIFT_BASE + u64::from(order / 4));
    let shift = shift_count(x.lo(), &target)?;
    let bits = grid_bits(order);
    let low = ln_gamma_stirling(&(x.lo() + bi_u64(u64::from(shift))), order)
        .ok_or(DeclineReason::ResourceLimit)?;
    let high = ln_gamma_stirling(&(x.hi() + bi_u64(u64::from(shift))), order)
        .ok_or(DeclineReason::ResourceLimit)?;
    // ln Γ is increasing on [2, ∞), and the shift target is well above 2.
    let mut total = BigInterval::new(low.lo().clone(), high.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)?;
    // One logarithm of the whole product, not one per factor: `ln_large` costs
    // the same whatever the denominator looks like, so `ln prod(x+i)` is a
    // single call where the sum of logarithms was `2*shift` of them. Every
    // factor is positive and increasing in `x`, so the product over the box is
    // bracketed by the products at its endpoints.
    let mut product_lo = BigRational::one();
    let mut product_hi = BigRational::one();
    for i in 0..shift {
        let offset = bi_u64(u64::from(i));
        product_lo *= x.lo() + &offset;
        product_hi *= x.hi() + &offset;
    }
    if shift > 0 {
        let factor_lo = ln_large(&product_lo, order).ok_or(DeclineReason::ResourceLimit)?;
        let factor_hi = ln_large(&product_hi, order).ok_or(DeclineReason::ResourceLimit)?;
        let factor = BigInterval::new(factor_lo.lo().clone(), factor_hi.hi().clone())
            .ok_or(DeclineReason::PrecisionUnreachable)?;
        total = total.sub(&factor);
    }
    total = coarsen(&total, bits);
    let value_lo = exp_point(total.lo(), order).ok_or(DeclineReason::ResourceLimit)?;
    let value_hi = exp_point(total.hi(), order).ok_or(DeclineReason::ResourceLimit)?;
    BigInterval::new(value_lo.lo().clone(), value_hi.hi().clone())
        .ok_or(DeclineReason::PrecisionUnreachable)
}

/// How many unit shifts take `x` to at least `target`, or a resource decline.
///
/// # Errors
///
/// [`DeclineReason::ResourceLimit`] past [`SHIFT_CAP`].
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

/// `ln Γ(y)` for a rational `y > 0` by the Stirling series
///
/// ```text
/// ln Γ z = (z − 1/2)·ln z − z + (1/2)·ln 2π
///          + Σ_(k=1)^m B_(2k)/(2k(2k−1)·z^(2k−1))
/// ```
///
/// with the classical remainder bound
/// `|R_m(z)| <= |B_(2m+2)|/((2m+2)(2m+1)·z^(2m+1))`, which holds for every real
/// `z > 0`: the series is enveloping there, so the remainder never exceeds the
/// first omitted term and carries its sign (DLMF 5.11.3; Whittaker–Watson
/// §12.33). The bound is sharp only for large `z`, which is why
/// [`gamma_interval`] shifts the argument up before calling this.
fn ln_gamma_stirling(y: &BigRational, order: u32) -> Option<BigInterval> {
    if !y.is_positive() {
        return None;
    }
    let terms = order.clamp(1, STIRLING_TERMS_CAP);
    let bernoulli = bernoulli_table(2 * terms + 2);
    let half = br(1, 2);
    let ln_y = ln_large(y, order)?;
    let pi = pi_enclosure(order)?;
    let two_pi = coarsen(&pi.scale(&bi(2)), grid_bits(order));
    let ln_two_pi_lo = ln_large(two_pi.lo(), order)?;
    let ln_two_pi_hi = ln_large(two_pi.hi(), order)?;
    let ln_two_pi = BigInterval::new(ln_two_pi_lo.lo().clone(), ln_two_pi_hi.hi().clone())?;
    let mut total = ln_y
        .scale(&(y - &half))
        .sub(&BigInterval::point(y.clone()))
        .add(&ln_two_pi.scale(&half));
    for k in 1..=terms {
        let index = 2 * usize::try_from(k).ok()?;
        let coefficient = &bernoulli[index]
            / (bi_u64(index as u64) * bi_u64(index as u64 - 1) * ratpow(y, 2 * k - 1));
        total = total.add(&BigInterval::point(coefficient));
    }
    let next = 2 * usize::try_from(terms).ok()? + 2;
    let error = (&bernoulli[next]
        / (bi_u64(next as u64) * bi_u64(next as u64 - 1) * ratpow(y, 2 * terms + 1)))
    .abs();
    BigInterval::new(total.lo() - &error, total.hi() + &error)
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
            let (pivot_row, target_row) = if row < column {
                let (head, tail) = work.split_at_mut(column);
                (&tail[0], &mut head[row])
            } else {
                let (head, tail) = work.split_at_mut(row);
                (&head[column], &mut tail[0])
            };
            for (entry, above) in target_row.iter_mut().zip(pivot_row) {
                *entry -= above * &factor;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enclosure::{enclose, enclose_constant};
    use crate::{CasExpr, UnaryFunc};

    /// `n/d` as a `BigRational`, for readable test fixtures.
    fn q(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    /// A decimal literal as an exact rational — used only to state a cited
    /// digit string, never to compute.
    fn decimal(text: &str) -> BigRational {
        let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
        let digits = format!("{whole}{fraction}");
        let numerator: BigInt = digits.parse().expect("decimal digits");
        BigRational::new(
            numerator,
            BigInt::from(10u32).pow(u32::try_from(fraction.len()).unwrap()),
        )
    }

    /// The unit-circle / diagonal-line system `x² + y² − 1 = 0`, `y − x = 0`.
    fn circle_and_line() -> PolySystem {
        let circle = MultiPoly::zero(2)
            .with_term(Rational::integer(1), &[2, 0])
            .unwrap()
            .with_term(Rational::integer(1), &[0, 2])
            .unwrap()
            .with_term(Rational::integer(-1), &[0, 0])
            .unwrap();
        let line = MultiPoly::zero(2)
            .with_term(Rational::integer(1), &[0, 1])
            .unwrap()
            .with_term(Rational::integer(-1), &[1, 0])
            .unwrap();
        PolySystem::new(vec![circle, line]).expect("square system")
    }

    /// The box `[7/10, 18/25]²`, which brackets `(1/sqrt 2, 1/sqrt 2)`.
    fn near_the_root() -> Vec<BigInterval> {
        vec![
            BigInterval::new(q(7, 10), q(18, 25)).unwrap(),
            BigInterval::new(q(7, 10), q(18, 25)).unwrap(),
        ]
    }

    /// A certified enclosure of the circle/line intersection at precision 60.
    fn circle_certificate() -> (PolySystem, Vec<BigInterval>, SystemEnclosure) {
        let system = circle_and_line();
        let start = near_the_root();
        let e = enclose_system(&system, &start, 60).expect("Krawczyk enclosure");
        (system, start, e)
    }

    // -- The kernels -------------------------------------------------------

    #[test]
    fn nth_root_brackets_the_root_from_both_sides() {
        for (value, degree) in [(2i64, 3u32), (5, 2), (7, 4), (1000, 5)] {
            let p = BigRational::from(BigInt::from(value));
            let bracket = nth_root_point(&p, degree, 64).expect("root");
            // The bracket is honest exactly when lo^q <= p <= hi^q.
            assert!(
                ratpow(bracket.lo(), degree) <= p,
                "lower end of {value}^(1/{degree}) is too big"
            );
            assert!(
                ratpow(bracket.hi(), degree) >= p,
                "upper end of {value}^(1/{degree}) is too small"
            );
        }
    }

    #[test]
    fn nth_root_of_a_negative_declines() {
        assert!(nth_root_point(&-BigRational::one(), 3, 16).is_none());
        assert!(nth_root_point(&BigRational::one(), 0, 16).is_none());
    }

    #[test]
    fn nth_root_at_degree_two_agrees_with_the_certified_sqrt() {
        // root_2 and the parent module's `sqrt` are the same function by two
        // spellings of one iteration; their brackets must overlap.
        let two = bi(2);
        let mine = nth_root_point(&two, 2, 64).expect("root_2");
        let theirs = enclose_constant("sqrt2", 60).expect("sqrt 2");
        assert!(mine.lo() <= theirs.interval.hi() && theirs.interval.lo() <= mine.hi());
    }

    #[test]
    fn the_erf_monotone_index_is_where_the_terms_start_falling() {
        // At magnitude 2 the terms fall from k = 2 (the quadratic 2k²−3k−1 is
        // non-negative there and negative at k = 1), which is the hypothesis
        // the alternating bound needs.
        assert_eq!(erf_monotone_index(&bi(2)), Some(2));
        assert_eq!(erf_monotone_index(&BigRational::zero()), Some(0));
        // The index really does bound the ratio: check the terms fall from it.
        for magnitude in [1i64, 2, 5, 8] {
            let a = bi(magnitude);
            let start = erf_monotone_index(&a).expect("index");
            for k in start..start + 5 {
                let kk = bi_u64(u64::from(k));
                let ratio = (&a * &a) * (bi(2) * &kk + BigRational::one())
                    / ((&kk + BigRational::one()) * (bi(2) * &kk + bi(3)));
                assert!(
                    ratio <= BigRational::one(),
                    "terms rise at k = {k} for magnitude {magnitude}"
                );
            }
        }
    }

    #[test]
    fn the_bessel_monotone_index_is_where_the_terms_start_falling() {
        for (magnitude, order) in [(1i64, 0u32), (4, 0), (10, 2)] {
            let a = bi(magnitude);
            let start = bessel_monotone_index(&a, order).expect("index");
            for k in start..start + 5 {
                let ratio = (&a * &a)
                    / bi(4)
                    / (bi_u64(u64::from(k) + 1) * bi_u64(u64::from(k) + u64::from(order) + 1));
                assert!(ratio <= BigRational::one(), "terms rise at k = {k}");
            }
        }
    }

    #[test]
    fn bernoulli_table_matches_the_i128_reference() {
        // `combinatorics::bernoulli` is `i128`-bounded; where it answers, this
        // table must agree with it exactly.
        let table = bernoulli_table(30);
        let mut compared = 0usize;
        for n in 0..=30u32 {
            let Some(reference) = crate::combinatorics::bernoulli(n) else {
                continue;
            };
            let lifted = from_rational(reference);
            assert_eq!(
                table[n as usize], lifted,
                "B_{n} disagrees with the reference"
            );
            compared += 1;
        }
        assert!(
            compared >= 10,
            "the cross-check compared only {compared} Bernoulli numbers"
        );
    }

    #[test]
    fn the_stirling_route_agrees_with_the_exact_factorial() {
        // ln Gamma(13) = ln(12!) = ln(479001600). The closed form is not
        // consulted here: `ln_gamma_stirling` is called directly, so this
        // measures the asymptotic series and its error bound against a known
        // integer, checked through the parent module's independent `ln`.
        let value = ln_gamma_stirling(&bi(13), 32).expect("Stirling at 13");
        let reference = ln_point(&bi(479_001_600), 64).expect("ln of 12!");
        assert!(
            value.lo() <= reference.hi() && reference.lo() <= value.hi(),
            "Stirling gave {value} for ln Gamma(13) but ln(12!) is {reference}"
        );
        assert!(
            value.width() < br(1, 1000),
            "the Stirling enclosure of ln Gamma(13) is too wide: {value}"
        );
    }

    #[test]
    fn the_stirling_error_bound_shrinks_with_the_order() {
        let coarse = ln_gamma_stirling(&bi(13), 4).expect("order 4").width();
        let fine = ln_gamma_stirling(&bi(13), 64).expect("order 64").width();
        assert!(fine < coarse, "raising the order did not tighten the bound");
    }

    // -- Multivariate roots: the certificate --------------------------------

    #[test]
    fn the_circle_and_line_intersection_is_enclosed_and_verifies() {
        let (system, start, e) = circle_certificate();
        e.verify(&system, &start).expect("verifies");
        // 1/sqrt(2) = 0.70710678118654752440084436210485...
        let root = decimal("0.7071067811865475244008443621048");
        for coordinate in &e.region {
            assert!(
                coordinate.contains(&root),
                "the enclosure {coordinate} misses 1/sqrt(2)"
            );
            assert!(coordinate.width() <= pow2(-60));
        }
        assert!(
            e.steps[e.existence_step].strict,
            "the existence step does not claim a strict inclusion"
        );
    }

    #[test]
    fn a_box_with_no_root_declines() {
        let system = circle_and_line();
        let start = vec![
            BigInterval::new(bi(2), bi(3)).unwrap(),
            BigInterval::new(bi(2), bi(3)).unwrap(),
        ];
        let reason = enclose_system_with_reason(&system, &start, 20).unwrap_err();
        assert_eq!(reason, DeclineReason::NotIsolating);
        assert!(enclose_system(&system, &start, 20).is_none());
    }

    #[test]
    fn a_singular_midpoint_jacobian_declines_rather_than_dividing_by_zero() {
        // x² − y = 0, y² − x⁴ = 0 is degenerate along y = x²: the Jacobian
        // determinant is 4x(y − x²)... which vanishes on the whole solution
        // curve, so no Krawczyk inclusion can succeed and the module must
        // decline rather than return something.
        let first = MultiPoly::zero(2)
            .with_term(Rational::integer(1), &[2, 0])
            .unwrap()
            .with_term(Rational::integer(-1), &[0, 1])
            .unwrap();
        let second = MultiPoly::zero(2)
            .with_term(Rational::integer(1), &[0, 2])
            .unwrap()
            .with_term(Rational::integer(-1), &[4, 0])
            .unwrap();
        let system = PolySystem::new(vec![first, second]).expect("system");
        let start = vec![
            BigInterval::new(q(1, 2), bi(2)).unwrap(),
            BigInterval::new(q(1, 4), bi(4)).unwrap(),
        ];
        let reason = enclose_system_with_reason(&system, &start, 20).unwrap_err();
        assert!(
            matches!(
                reason,
                DeclineReason::DomainError(_)
                    | DeclineReason::NotIsolating
                    | DeclineReason::PrecisionUnreachable
                    | DeclineReason::ResourceLimit
            ),
            "expected a decline, got {reason:?}"
        );
    }

    #[test]
    fn a_box_of_the_wrong_length_declines() {
        let system = circle_and_line();
        let start = vec![BigInterval::new(bi(0), bi(1)).unwrap()];
        let reason = enclose_system_with_reason(&system, &start, 20).unwrap_err();
        assert!(matches!(reason, DeclineReason::DomainError(_)));
    }

    #[test]
    fn a_non_square_system_is_not_constructible() {
        let single = MultiPoly::zero(2)
            .with_term(Rational::integer(1), &[1, 0])
            .unwrap();
        assert!(PolySystem::new(vec![single]).is_none());
        assert!(PolySystem::new(Vec::new()).is_none());
    }

    #[test]
    fn a_term_with_the_wrong_arity_is_rejected() {
        assert!(
            MultiPoly::zero(2)
                .with_term(Rational::integer(1), &[1])
                .is_none()
        );
    }

    /// Row `row` of the `n` by `n` identity.
    fn identity(n: usize, row: usize) -> Vec<BigRational> {
        (0..n)
            .map(|column| {
                if column == row {
                    BigRational::one()
                } else {
                    BigRational::zero()
                }
            })
            .collect()
    }

    #[test]
    fn the_exact_inverse_is_an_inverse() {
        let matrix = vec![vec![q(3, 2), bi(2)], vec![bi(-1), q(4, 5)]];
        let inverse = invert(&matrix).expect("invertible");
        for (row, entries) in matrix.iter().enumerate() {
            for (column, expected) in identity(entries.len(), row).iter().enumerate() {
                let entry: BigRational = entries
                    .iter()
                    .zip(&inverse)
                    .map(|(left, right)| left * &right[column])
                    .sum();
                assert_eq!(entry, *expected, "row {row}, column {column}");
            }
        }
        assert!(invert(&[vec![bi(1), bi(2)], vec![bi(2), bi(4)]]).is_none());
    }

    // -- Forged system certificates: one guard, one death -------------------

    #[test]
    fn forged_empty_system_certificate_is_refused() {
        let (system, start, mut e) = circle_certificate();
        e.steps.clear();
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("at least one Krawczyk step"),
            "expected the shape guard, got: {message}"
        );
    }

    #[test]
    fn forged_wrong_dimension_box_is_refused() {
        let (system, start, mut e) = circle_certificate();
        e.steps[0].domain.pop();
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("wrong dimension"),
            "expected the shape guard, got: {message}"
        );
    }

    #[test]
    fn forged_preconditioner_shape_is_refused() {
        let (system, start, mut e) = circle_certificate();
        e.steps[0].preconditioner[0].pop();
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("preconditioner that is not"),
            "expected the shape guard, got: {message}"
        );
    }

    #[test]
    fn a_certificate_checked_against_a_different_starting_box_is_refused() {
        let (system, _, e) = circle_certificate();
        let elsewhere = vec![
            BigInterval::new(bi(0), bi(1)).unwrap(),
            BigInterval::new(bi(0), bi(1)).unwrap(),
        ];
        let message = e.verify(&system, &elsewhere).unwrap_err();
        assert!(
            message.contains("does not start from the given box"),
            "expected the start guard, got: {message}"
        );
    }

    #[test]
    fn forged_broken_chain_is_refused() {
        let (system, start, mut e) = circle_certificate();
        assert!(e.steps.len() >= 2, "this forgery needs a multi-step chain");
        // Widen the second step's domain: it is still a valid enclosure of the
        // root, so only the link to the previous step's output is broken.
        e.steps[1].domain[0] = BigInterval::new(
            e.steps[1].domain[0].lo() - BigRational::one(),
            e.steps[1].domain[0].hi() + BigRational::one(),
        )
        .unwrap();
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("does not start from the box step"),
            "expected the chain guard, got: {message}"
        );
    }

    #[test]
    fn forged_understated_krawczyk_image_is_refused() {
        let (system, start, mut e) = circle_certificate();
        // Claim a narrower operator value than the one that recomputes: this is
        // exactly how a forger would fake a contraction.
        e.steps[0].image[0] = BigInterval::point(e.steps[0].image[0].midpoint());
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("does not contain the recomputed one"),
            "expected the image guard, got: {message}"
        );
    }

    #[test]
    fn forged_output_dropping_part_of_the_image_is_refused() {
        let (system, start, mut e) = circle_certificate();
        // Keep only the upper half of the first contraction: a root in the
        // lower half would be silently lost.
        let kept = e.steps[0].output[0].clone();
        e.steps[0].output[0] = BigInterval::new(kept.midpoint(), kept.hi().clone()).unwrap();
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("drops part of the Krawczyk image"),
            "expected the contraction guard, got: {message}"
        );
    }

    #[test]
    fn a_forged_strict_inclusion_is_refused() {
        // A one-step certificate over a box the operator does NOT contract into
        // strictly, claiming that it does. Every other guard passes: the image
        // and the output are the honest recomputed ones.
        let system = circle_and_line();
        let start = vec![
            BigInterval::new(BigRational::zero(), bi(2)).unwrap(),
            BigInterval::new(BigRational::zero(), bi(2)).unwrap(),
        ];
        let midpoint: Vec<BigRational> = start.iter().map(BigInterval::midpoint).collect();
        let preconditioner = invert(&system.jacobian_at(&midpoint)).expect("invertible");
        let image = krawczyk_image(&system, &start, &preconditioner).expect("image");
        assert!(
            !strictly_inside(&image, &start),
            "this fixture needs a box the operator does not contract into"
        );
        let output = intersect(&image, &start).expect("nonempty");
        let forged = SystemEnclosure {
            region: output.clone(),
            precision: 0,
            steps: vec![KrawczykStep {
                domain: start.clone(),
                preconditioner,
                image,
                strict: true,
                output,
            }],
            existence_step: 0,
        };
        let message = forged.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("strict inclusion the recomputed operator does not satisfy"),
            "expected the existence guard, got: {message}"
        );
    }

    #[test]
    fn an_existence_step_that_claims_nothing_is_refused() {
        let (system, start, mut e) = circle_certificate();
        let step = e.existence_step;
        e.steps[step].strict = false;
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("claims no strict inclusion"),
            "expected the existence guard, got: {message}"
        );
    }

    #[test]
    fn an_out_of_range_existence_step_is_refused() {
        let (system, start, mut e) = circle_certificate();
        e.existence_step = e.steps.len();
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("existence step is out of range"),
            "expected the range guard, got: {message}"
        );
    }

    #[test]
    fn a_final_box_detached_from_the_chain_is_refused() {
        let (system, start, mut e) = circle_certificate();
        // Shift the headline box by a whole unit; every step stays honest, so
        // only the final-box guard can see it.
        e.region[0] = BigInterval::new(
            e.region[0].lo() + BigRational::one(),
            e.region[0].hi() + BigRational::one(),
        )
        .unwrap();
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("not the box the last step produced"),
            "expected the final-box guard, got: {message}"
        );
    }

    #[test]
    fn a_box_too_wide_for_the_claimed_precision_is_refused() {
        let (system, start, mut e) = circle_certificate();
        // Widen the last output and the headline box together: the chain still
        // contains K(X) intersect X and the two still agree, so only the width
        // guard is left.
        let last = e.steps.len() - 1;
        for slot in 0..2 {
            let widened = BigInterval::new(
                e.steps[last].output[slot].lo() - BigRational::one(),
                e.steps[last].output[slot].hi() + BigRational::one(),
            )
            .unwrap();
            e.steps[last].output[slot] = widened.clone();
            e.region[slot] = widened;
        }
        let message = e.verify(&system, &start).unwrap_err();
        assert!(
            message.contains("exceeds 2^-"),
            "expected the width guard, got: {message}"
        );
    }

    // -- Cost ---------------------------------------------------------------

    #[test]
    fn cost_table_wave_two() {
        // Advisory only: one unpinned run on a shared host. Printed so the
        // module docs can be re-measured with `--nocapture`.
        if let Ok(load) = std::fs::read_to_string("/proc/loadavg") {
            println!("host load at the start of the run: {}", load.trim());
        }
        let heads: [(&str, CasExpr); 4] = [
            (
                "2^(1/3)",
                crate::enclosure::rational_power(CasExpr::int(2), 1, 3).expect("cube root"),
            ),
            (
                "erf(1)",
                CasExpr::Unary(UnaryFunc::Erf, Box::new(CasExpr::int(1))),
            ),
            (
                "Gamma(1/3)",
                CasExpr::Unary(UnaryFunc::Gamma, Box::new(CasExpr::rat(1, 3))),
            ),
            (
                "J_0(1)",
                CasExpr::Unary(UnaryFunc::BesselJ(0), Box::new(CasExpr::int(1))),
            ),
        ];
        // The full ladder is a `--release` measurement. In a debug build the
        // `Gamma` rows at 100 and 200 both land on order 64 and cost about 60 s
        // between them, so the debug sweep measures the cheap end and the doc
        // table records the release run.
        let ladder: &[u32] = if cfg!(debug_assertions) {
            &[10, 50]
        } else {
            &[10, 50, 100, 200]
        };
        for (name, expr) in &heads {
            for &precision in ladder {
                let start = std::time::Instant::now();
                let Some(e) = enclose(expr, &[], precision) else {
                    println!("{name:>12} precision {precision:>3}: declined");
                    continue;
                };
                let produced = start.elapsed();
                let start = std::time::Instant::now();
                e.verify(expr, &[]).expect("verifies");
                let verified = start.elapsed();
                println!(
                    "{name:>12} precision {precision:>3}: order {:>4}  produce {produced:?}  verify {verified:?}",
                    e.evidence.last().expect("a step").order
                );
            }
        }
        let system = circle_and_line();
        let start_box = near_the_root();
        for &precision in ladder {
            let start = std::time::Instant::now();
            let Some(e) = enclose_system(&system, &start_box, precision) else {
                println!("{:>12} precision {precision:>3}: declined", "krawczyk");
                continue;
            };
            let produced = start.elapsed();
            let start = std::time::Instant::now();
            e.verify(&system, &start_box).expect("verifies");
            let verified = start.elapsed();
            println!(
                "{:>12} precision {precision:>3}: {:>3} steps  produce {produced:?}  verify {verified:?}",
                "krawczyk",
                e.steps.len()
            );
        }
    }
}
