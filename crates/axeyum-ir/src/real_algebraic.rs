//! Real algebraic numbers as a defining polynomial plus an isolating interval
//! (ADR-0038; arbitrary-precision storage per ADR-0045).
//!
//! A [`RealAlgebraic`] is an *exact*, irrational-capable real value: an integer
//! polynomial `poly` (LSB-first, mirroring the NRA/NIA `Poly` layout) together
//! with a rational open interval `(lo, hi)` that contains **exactly one** real
//! root of `poly`. That unique root *is* the value. The single-root invariant is
//! established by construction (a sign change of `poly` between the endpoints,
//! the interval already isolated from any other root by the decider's root
//! isolation).
//!
//! **Storage (ADR-0045):** the defining polynomial is `Vec<BigInt>` and the
//! interval endpoints are [`axeyum_arith::big::BigRational`] — arbitrary precision.
//! This removes the former `i128`-storage ceiling: algebraic field arithmetic
//! (`add`/`mul`/`neg`) computes entirely in bignum (via the `crate::poly_big`
//! primitives), so higher-degree coupled NRA witnesses (e.g. the degree-4
//! nested-radical coordinates of `x²+y²=4 ∧ x·y=1`) now decide instead of
//! declining on an intermediate-or-final overflow. Algebraic values appear only in
//! NRA witnesses (rare), so the always-bignum storage is fine; the core
//! [`Rational`] type (used everywhere) stays `i128`.
//!
//! The operations the single-variable NRA decider needs to build and
//! **replay-check** an irrational witness:
//!
//! - [`RealAlgebraic::sign_at`] — the exact sign of an arbitrary integer
//!   polynomial `q` evaluated at this algebraic number `α`, by **interval
//!   refinement**: repeatedly bisect `(lo, hi)` (keeping the half that still
//!   brackets the root of the *defining* `poly`) until `q` has a constant nonzero
//!   sign across the whole refined interval. `q ≡ poly` (or any `q` that vanishes
//!   at `α`) is detected and reported as sign `0`.
//! - [`RealAlgebraic::compare_rational`] — compare `α` against a rational `c` by
//!   refining until `c` falls outside `(lo, hi)`, or detecting `poly(c) = 0`
//!   (then `α = c`, since `α` is the interval's sole root).
//! - algebraic field arithmetic ([`RealAlgebraic::neg`], [`RealAlgebraic::add`],
//!   [`RealAlgebraic::mul`]) — the exact `−α`, `α + β`, `α · β` via the
//!   resultant + squarefree + Sturm-isolation primitives in `crate::poly_big`,
//!   computed in arbitrary precision.
//!
//! **No floating point anywhere.** Every sign test is exact over `BigInt` /
//! [`BigRational`]. Refinement is bounded; a failure to converge within the bound
//! returns `None`, and the caller declines (a sound `unknown`) rather than risk a
//! wrong answer. The resultant/Sturm work is bounded by degree/dimension caps in
//! `crate::poly_big` → graceful decline, never OOM/hang.

use core::cmp::Ordering;

use axeyum_arith::big::BigInt;
use axeyum_arith::big::BigRational;
use axeyum_arith::big::Zero;

use crate::poly_big::{
    BigAlgebraic, Combine, RootCounter, big_eval_int_at, big_poly_divides, big_root_object,
    big_sign, bigint_poly_from_i128, bigrational_from_i128, combine_retry,
};
use crate::rational::Rational;

/// The maximum number of bisection steps [`RealAlgebraic::sign_at`] and
/// [`RealAlgebraic::compare_rational`] will take before giving up (returning
/// `None` → the caller declines). Each step halves the interval, so the
/// resolution after `N` steps is `(hi − lo) / 2^N`; 256 steps is far more than
/// enough to separate any root the decider produces from a distinct sign of a
/// bounded polynomial, while staying cheap.
const MAX_REFINE_STEPS: u32 = 256;

/// The sign of a polynomial value at a point: negative, zero, or positive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sign {
    /// Strictly negative.
    Neg,
    /// Exactly zero.
    Zero,
    /// Strictly positive.
    Pos,
}

/// A real algebraic number: the unique real root of `poly` lying in the open
/// interval `(lo, hi)`.
///
/// Invariant (established by [`RealAlgebraic::new`] / [`RealAlgebraic::new_big`]):
/// `poly` has *exactly one* real root in `(lo, hi)`, witnessed by
/// `sign(poly(lo)) ≠ sign(poly(hi))` (both nonzero), and the interval is otherwise
/// root-isolated by the caller. The value denoted is that root.
#[derive(Debug, Clone)]
pub struct RealAlgebraic {
    /// The arbitrary-precision data is held behind a single [`Box`] so the
    /// [`RealAlgebraic`] (and hence [`crate::Value`]) stays a one-pointer-wide,
    /// cheaply-`Clone`/`Copy`-adjacent handle: the bignum polynomial and interval
    /// are large, and inlining them would bloat every `Value`-carrying enum (and
    /// trip `result_large_err`). Algebraic values are rare (NRA witnesses only), so
    /// the extra indirection is irrelevant.
    inner: Box<Repr>,
}

/// The heap-allocated payload of a [`RealAlgebraic`].
#[derive(Debug, Clone)]
struct Repr {
    /// The defining integer polynomial, LSB-first (`coeffs[i]` is the coefficient
    /// of `xⁱ`), in arbitrary precision. Trailing zeros are not required to be
    /// trimmed, but the leading coefficient must be nonzero for the degree to be
    /// meaningful.
    poly: Vec<BigInt>,
    /// The lower endpoint of the isolating interval (exclusive).
    lo: BigRational,
    /// The upper endpoint of the isolating interval (exclusive).
    hi: BigRational,
}

/// The sign of a [`BigRational`] as a [`Sign`].
fn sign_of_big(r: &BigRational) -> Sign {
    big_sign(r)
}

impl RealAlgebraic {
    /// Builds a real algebraic number from an `i128` defining polynomial and an
    /// `i128`-[`Rational`] isolating interval `(lo, hi)`, lifting both to arbitrary
    /// precision. This convenience constructor keeps the `i128`-producing root
    /// isolation in the solver unchanged. Returns `None` if the one-root invariant
    /// cannot be confirmed (see [`RealAlgebraic::new_big`]).
    #[must_use]
    pub fn new(poly: Vec<i128>, lo: Rational, hi: Rational) -> Option<RealAlgebraic> {
        let poly = poly.into_iter().map(BigInt::from).collect();
        let lo = bigrational_from_i128(lo.numerator(), lo.denominator());
        let hi = bigrational_from_i128(hi.numerator(), hi.denominator());
        RealAlgebraic::new_big(poly, lo, hi)
    }

    /// Builds a real algebraic number from a bignum defining polynomial and an
    /// arbitrary-precision isolating interval `(lo, hi)`, returning `None` if the
    /// one-root invariant cannot be confirmed: `lo < hi`, and the polynomial must
    /// take a *strictly opposite, nonzero* sign at the two endpoints (a sign change
    /// ⇒ at least one root; the caller guarantees isolation ⇒ exactly one).
    ///
    /// The endpoint sign-change check is exact (Horner over [`BigRational`]). If
    /// `poly(lo)` or `poly(hi)` is zero, the endpoint *is* the root — but the
    /// interval is open, so the caller should instead represent that exact rational
    /// root as `Value::Real`; here we reject it (`None`).
    #[must_use]
    pub fn new_big(poly: Vec<BigInt>, lo: BigRational, hi: BigRational) -> Option<RealAlgebraic> {
        if lo >= hi {
            return None;
        }
        let slo = sign_of_big(&big_eval_int_at(&poly, &lo));
        let shi = sign_of_big(&big_eval_int_at(&poly, &hi));
        // Strict opposite, nonzero signs ⇒ a root strictly inside (lo, hi).
        match (slo, shi) {
            (Sign::Neg, Sign::Pos) | (Sign::Pos, Sign::Neg) => Some(RealAlgebraic {
                inner: Box::new(Repr { poly, lo, hi }),
            }),
            _ => None,
        }
    }

    /// Represent a **rational** `c` as a degree-1 algebraic number: the unique
    /// root of `q·x − p` (where `c = p/q`, `q > 0`) in the open interval
    /// `(c − 1, c + 1)`. Used to lift a rational operand of algebraic field
    /// arithmetic into the common [`RealAlgebraic`] form. `None` on overflow.
    ///
    /// (The value is rational, so the result's `compare_rational(&c)` is `Equal`;
    /// it is a structurally-valid single-root bracket — the field-arithmetic
    /// resultant treats it uniformly.)
    #[must_use]
    pub fn from_rational(c: Rational) -> Option<RealAlgebraic> {
        // `c = p / q` with q > 0 (Rational keeps the denominator positive).
        let p = c.numerator();
        let q = c.denominator();
        // poly = q·x − p (LSB-first [−p, q]); root is exactly c.
        let poly = vec![BigInt::from(-p), BigInt::from(q)];
        // The bracket (c − 1, c + 1), built directly in bignum.
        let c_big = bigrational_from_i128(p, q);
        let one = BigRational::from(BigInt::from(1));
        let lo = &c_big - &one;
        let hi = &c_big + &one;
        RealAlgebraic::new_big(poly, lo, hi)
    }

    /// The defining polynomial (LSB-first bignum-integer coefficients).
    #[must_use]
    pub fn defining_poly(&self) -> &[BigInt] {
        &self.inner.poly
    }

    /// The defining polynomial as `i128` coefficients, or `None` if any coefficient
    /// does not fit `i128`. Used by the solver's `i128`-backed NRA post-processing
    /// (rationalization, affine maps, coarsening): on `None` those paths decline
    /// soundly (a sound `Unknown`), never a wrong verdict.
    #[must_use]
    pub fn defining_poly_i128(&self) -> Option<Vec<i128>> {
        let mut out = Vec::with_capacity(self.inner.poly.len());
        for c in &self.inner.poly {
            out.push(i128::try_from(c.clone()).ok()?);
        }
        Some(out)
    }

    /// The current isolating interval `(lo, hi)` as `i128` [`Rational`]s, or `None`
    /// if either endpoint does not fit `i128`.
    #[must_use]
    pub fn interval(&self) -> Option<(Rational, Rational)> {
        Some((
            bigrational_to_rational(&self.inner.lo)?,
            bigrational_to_rational(&self.inner.hi)?,
        ))
    }

    /// The current isolating interval `(lo, hi)` in arbitrary precision.
    #[must_use]
    pub fn interval_big(&self) -> (BigRational, BigRational) {
        (self.inner.lo.clone(), self.inner.hi.clone())
    }

    /// Refine the isolating interval *in place* by one bisection step: evaluate
    /// the defining polynomial at the midpoint and keep the half whose endpoints
    /// still straddle the root. Returns `Sign::Zero` if the midpoint *is* the root
    /// (then the value is exactly rational and both endpoints collapse to it), or
    /// the midpoint sign for a successful narrowing.
    fn refine_once(&mut self) -> Sign {
        let two = BigRational::from(BigInt::from(2));
        let mid = (&self.inner.lo + &self.inner.hi) / two;
        let smid = sign_of_big(&big_eval_int_at(&self.inner.poly, &mid));
        if smid == Sign::Zero {
            self.inner.lo = mid.clone();
            self.inner.hi = mid;
            return Sign::Zero;
        }
        let slo = sign_of_big(&big_eval_int_at(&self.inner.poly, &self.inner.lo));
        if slo == smid {
            self.inner.lo = mid;
        } else {
            self.inner.hi = mid;
        }
        smid
    }

    /// The exact [`Sign`] of an arbitrary integer polynomial `q` (given as `i128`
    /// coefficients) evaluated at this algebraic number `α`.
    ///
    /// Strategy (exact, no float): if the defining polynomial divides `q` exactly
    /// over the rationals, then `q(α) = 0` (every root of `poly`, in particular α,
    /// is a root of `q`). This is the only sound way to report `Zero` for an
    /// irrational α. Otherwise refine the isolating interval until `q`'s sign is
    /// constant and nonzero across the bracket, or the interval collapses onto an
    /// exact rational root where `q` can be evaluated directly.
    ///
    /// Returns `None` (→ the caller declines, a sound `unknown`) if a constant
    /// nonzero sign is not reached within `MAX_REFINE_STEPS`.
    #[must_use]
    pub fn sign_at(&self, q: &[i128]) -> Option<Sign> {
        let qbig = bigint_poly_from_i128(q);
        self.sign_at_big(&qbig)
    }

    /// As [`RealAlgebraic::sign_at`] but for a bignum-integer polynomial `q`.
    ///
    /// # The side condition on the endpoint read, and why it is not optional
    ///
    /// The bracket `(lo, hi)` isolates `α` as a root of **this** number's
    /// defining polynomial. It says nothing about `q`. So agreeing, nonzero
    /// signs at `q(lo)` and `q(hi)` do **not** imply that `q` holds that sign
    /// across the bracket — they are two point samples, not an enclosure of
    /// `q`'s range, and `q` may have an even number of roots inside and dip
    /// through the opposite sign between them, exactly where `α` may lie.
    ///
    /// Concretely, for `α = √2` bracketed by `(1, 2)` and
    /// `q = 25x² − 70x + 48 = (5x − 6)(5x − 8)`: `q(1) = 3 > 0` and
    /// `q(2) = 8 > 0`, while `q(√2) ≈ −0.995 < 0`. Reading the endpoints alone
    /// answers `Pos` for a value that is `Neg`. That is a wrong sign in the
    /// trusted evaluation path, and `regression_two_roots_inside_the_bracket`
    /// pins it.
    ///
    /// So the endpoint read is accepted only alongside the exact side condition
    /// [`big_no_root_in_open`]: `q` has no root strictly inside the bracket. With
    /// that, the intermediate value theorem gives `q` a constant nonzero sign on
    /// the whole interval, so the answer holds for every point in it — including
    /// `α`, wherever in the bracket it sits. No separation bound is needed, and
    /// no "the interval got small" heuristic is used: a small interval is not
    /// evidence, a root count is.
    ///
    /// When the side condition cannot be decided exactly, this keeps refining
    /// (a narrower bracket may separate the endpoints' signs outright) and
    /// finally returns `None` — a decline, never a guess.
    #[must_use]
    pub fn sign_at_big(&self, q: &[BigInt]) -> Option<Sign> {
        // Exact vanishing test: `poly | q` over the rationals ⇒ q(α) = 0.
        if big_poly_divides(&self.inner.poly, q) {
            return Some(Sign::Zero);
        }
        // Built once and reused across bisections: the bracket narrows, the
        // polynomial does not.
        let counter = RootCounter::new(q);
        let mut probe = self.clone();
        for _ in 0..MAX_REFINE_STEPS {
            let vlo = big_eval_int_at(q, &probe.inner.lo);
            let vhi = big_eval_int_at(q, &probe.inner.hi);
            if probe.inner.lo == probe.inner.hi {
                return Some(sign_of_big(&vlo));
            }
            let slo = sign_of_big(&vlo);
            let shi = sign_of_big(&vhi);
            if slo == shi
                && slo != Sign::Zero
                && counter
                    .as_ref()
                    .and_then(|c| c.no_root_in_open(&probe.inner.lo, &probe.inner.hi))
                    == Some(true)
            {
                return Some(slo);
            }
            if probe.refine_once() == Sign::Zero {
                // Interval collapsed onto an exact rational root r of poly: α = r.
                let qr = big_eval_int_at(q, &probe.inner.lo);
                return Some(sign_of_big(&qr));
            }
        }
        None
    }

    /// Compare this algebraic number `α` against a rational `c`.
    ///
    /// Refines the isolating interval until `c` lies strictly outside `(lo, hi)`
    /// (then the comparison is decided by which side), or detects `poly(c) = 0`
    /// (then `c` is *a* root of the defining poly inside the bracket, hence `α`
    /// itself by isolation ⇒ [`Ordering::Equal`]).
    ///
    /// Returns `None` (→ decline) on non-convergence within `MAX_REFINE_STEPS`.
    #[must_use]
    pub fn compare_rational(&self, c: &Rational) -> Option<Ordering> {
        let c_big = bigrational_from_i128(c.numerator(), c.denominator());
        self.compare_big(&c_big)
    }

    /// As [`RealAlgebraic::compare_rational`] but against a [`BigRational`].
    #[must_use]
    pub fn compare_big(&self, c: &BigRational) -> Option<Ordering> {
        // If `c` is a root of the defining poly inside the (open) bracket, it is α.
        if *c > self.inner.lo
            && *c < self.inner.hi
            && sign_of_big(&big_eval_int_at(&self.inner.poly, c)) == Sign::Zero
        {
            return Some(Ordering::Equal);
        }
        let mut probe = self.clone();
        for _ in 0..MAX_REFINE_STEPS {
            if *c <= probe.inner.lo {
                return Some(Ordering::Greater);
            }
            if *c >= probe.inner.hi {
                return Some(Ordering::Less);
            }
            if probe.refine_once() == Sign::Zero {
                return Some(probe.inner.lo.cmp(c));
            }
        }
        None
    }

    /// The **root-object** form of this number: its squarefree, primitive,
    /// positive-leading defining polynomial (LSB-first bignum integers) and the
    /// 1-based index of this root among that polynomial's distinct real roots in
    /// ascending order.
    ///
    /// This is the only exact, portable way to *name* an irrational value. The
    /// pair `(p, k)` denotes "the k-th smallest real root of p", which is what
    /// z3 writes as `(root-obj p k)`
    /// (`references/z3/src/math/polynomial/algebraic_numbers.cpp:3216-3224`).
    /// Both halves are canonical, so two [`RealAlgebraic`]s denoting the same
    /// number produce the same pair regardless of how their brackets were
    /// refined or how their stored polynomial was scaled.
    ///
    /// `None` when no exact answer can be formed (the degree guard, a Sturm
    /// chain that does not close). A caller that cannot get a root object must
    /// **decline to print the value** -- rounding an algebraic coordinate to a
    /// nearby rational produces a model that does not satisfy the query.
    #[must_use]
    pub fn root_object(&self) -> Option<(Vec<BigInt>, usize)> {
        big_root_object(&self.inner.poly, &self.inner.lo)
    }

    /// A rational strictly inside the current isolating interval — the interval
    /// midpoint — usable as a coarse numeric stand-in (never used for any sign
    /// decision, only for display/diagnostics). `None` if it does not fit `i128`.
    #[must_use]
    pub fn approx_midpoint(&self) -> Option<Rational> {
        let two = BigRational::from(BigInt::from(2));
        let mid = (&self.inner.lo + &self.inner.hi) / two;
        bigrational_to_rational(&mid)
    }

    // ========================================================================
    // Algebraic field arithmetic (ADR-0038, slice 3; ADR-0045 storage): −α,
    // α+β, α·β — now computed entirely in arbitrary precision via
    // `crate::poly_big`. The former i128-fast-path / bignum-retry SPLIT collapses
    // into a single bignum computation: there is no overflow decline on the
    // algebraic arithmetic path, so the headline nested-radical combinations
    // decide. Each returns `Option<RealAlgebraic>`, declining (`None`) only on a
    // degree/dimension/round-cap trip in `poly_big` (graceful decline, never a
    // wrong value). The single-root invariant of the result is re-established by an
    // EXACT Sturm count == 1 with strict opposite-sign endpoints (inside
    // `combine_retry`), exactly as `RealAlgebraic::new_big` requires.
    // ========================================================================

    /// The exact additive inverse `−α`.
    ///
    /// If `α` is the unique root of `p(x)` in `(lo, hi)`, then `−α` is the unique
    /// root of `p(−x)` in `(−hi, −lo)`. `p(−x)` flips the sign of every odd-degree
    /// coefficient. Exact (bignum never overflows).
    #[must_use]
    pub fn neg(&self) -> Option<RealAlgebraic> {
        let mut poly = Vec::with_capacity(self.inner.poly.len());
        for (i, c) in self.inner.poly.iter().enumerate() {
            if i % 2 == 1 {
                poly.push(-c.clone());
            } else {
                poly.push(c.clone());
            }
        }
        let lo = -self.inner.hi.clone();
        let hi = -self.inner.lo.clone();
        RealAlgebraic::new_big(poly, lo, hi)
    }

    /// The exact sum `α + β`, computed in arbitrary precision (no float). `α + β`
    /// is the unique root of the squarefree part of `Res_y(p_α(y), p_β(x − y))`
    /// inside the sum of the operand intervals, isolated by an exact Sturm count.
    /// `None` on a degree/dimension/round-cap trip.
    #[must_use]
    pub fn add(&self, other: &RealAlgebraic) -> Option<RealAlgebraic> {
        self.combine(other, Combine::Sum)
    }

    /// The exact product `α · β`, computed in arbitrary precision (no float). A
    /// [`RealAlgebraic`] is irrational by construction (never the rational `0`), so
    /// `α · β` is the unique root of the squarefree part of the homogenized
    /// resultant `Res_y(p_α(y), y^{deg β}·p_β(x / y))` inside the product of the
    /// operand intervals. `None` on a degree/dimension/round-cap trip.
    #[must_use]
    pub fn mul(&self, other: &RealAlgebraic) -> Option<RealAlgebraic> {
        self.combine(other, Combine::Product)
    }

    /// Shared driver for `add`/`mul`: run the bignum resultant → squarefree →
    /// Sturm-isolation, then wrap the result as a `RealAlgebraic`.
    fn combine(&self, other: &RealAlgebraic, how: Combine) -> Option<RealAlgebraic> {
        let BigAlgebraic { poly, lo, hi } = combine_retry(
            &self.inner.poly,
            &self.inner.lo,
            &self.inner.hi,
            &other.inner.poly,
            &other.inner.lo,
            &other.inner.hi,
            how,
        )?;
        // Re-establish the single-root invariant on the returned interval
        // (defense-in-depth: `combine_retry` already confirmed exactly one root
        // with opposite endpoint signs).
        RealAlgebraic::new_big(poly, lo, hi)
    }
}

/// `BigRational` → `i128` [`Rational`], `None` if numerator or denominator is out
/// of `i128` range. The bignum rational is already in lowest terms.
fn bigrational_to_rational(r: &BigRational) -> Option<Rational> {
    let num = i128::try_from(r.numer().clone()).ok()?;
    let den = i128::try_from(r.denom().clone()).ok()?;
    Rational::checked_new(num, den)
}

/// The number of coefficients up to and including the highest nonzero one (the
/// "trimmed length"); `0` for the zero polynomial.
fn trimmed_len(coeffs: &[BigInt]) -> usize {
    let mut n = coeffs.len();
    while n > 0 && coeffs[n - 1].is_zero() {
        n -= 1;
    }
    n
}

/// Whether two LSB-first bignum-integer polynomials are equal up to trailing
/// zeros.
fn same_poly(a: &[BigInt], b: &[BigInt]) -> bool {
    let n = a.len().max(b.len());
    let zero = BigInt::from(0);
    (0..n).all(|i| a.get(i).unwrap_or(&zero) == b.get(i).unwrap_or(&zero))
}

/// Two algebraic numbers are equal iff they share a defining polynomial (up to
/// trailing zeros) **and** isolate the same root — which, for equal polynomials,
/// holds iff their isolating intervals overlap (each contains exactly one root of
/// the shared poly, so overlapping intervals must bracket the *same* root).
impl PartialEq for RealAlgebraic {
    fn eq(&self, other: &Self) -> bool {
        if !same_poly(&self.inner.poly, &other.inner.poly) {
            return false;
        }
        // Same poly: equal iff the open intervals overlap (both isolate one root).
        let lo = self.inner.lo.clone().max(other.inner.lo.clone());
        let hi = self.inner.hi.clone().min(other.inner.hi.clone());
        lo < hi
    }
}

impl Eq for RealAlgebraic {}

/// Hash on the defining polynomial only (a value-consistent coarsening of `Eq`:
/// equal values share a poly, so they hash equal; distinct roots of the same poly
/// also collide, which is permitted — `Hash` only requires `a == b ⇒ hash(a) ==
/// hash(b)`).
impl core::hash::Hash for RealAlgebraic {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        // Hash the trimmed coefficient sequence so trailing zeros do not perturb
        // the hash of otherwise-equal polynomials.
        let n = trimmed_len(&self.inner.poly);
        self.inner.poly[..n].hash(state);
    }
}

impl core::fmt::Display for RealAlgebraic {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "root of ")?;
        write_poly(f, &self.inner.poly)?;
        write!(
            f,
            " in ({}, {})",
            fmt_big(&self.inner.lo),
            fmt_big(&self.inner.hi)
        )
    }
}

/// Render a [`BigRational`] as `n` (integer) or `n/d`.
fn fmt_big(r: &BigRational) -> String {
    use axeyum_arith::big::One;
    if r.denom().is_one() {
        r.numer().to_string()
    } else {
        format!("{}/{}", r.numer(), r.denom())
    }
}

/// Render an LSB-first bignum-integer polynomial as a human-readable
/// `… + a·x^k + …` (descending degree), used only by [`RealAlgebraic`]'s
/// `Display`.
fn write_poly(f: &mut core::fmt::Formatter<'_>, coeffs: &[BigInt]) -> core::fmt::Result {
    let mut last = coeffs.len();
    while last > 1 && coeffs[last - 1].is_zero() {
        last -= 1;
    }
    let mut first = true;
    for i in (0..last).rev() {
        let c = &coeffs[i];
        if c.is_zero() {
            continue;
        }
        let neg = c.sign() == axeyum_arith::big::Sign::Minus;
        if first {
            write!(f, "{c}")?;
            first = false;
        } else if neg {
            write!(f, " - {}", -c)?;
        } else {
            write!(f, " + {c}")?;
        }
        match i {
            0 => {}
            1 => write!(f, "*x")?,
            _ => write!(f, "*x^{i}")?,
        }
    }
    if first {
        write!(f, "0")?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `x² − 2` over (1, 2) is `+√2`.
    fn sqrt2() -> RealAlgebraic {
        RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(1), Rational::integer(2)).unwrap()
    }

    #[test]
    fn new_requires_sign_change() {
        // No sign change of x²−2 over (2, 3): both positive ⇒ rejected.
        assert!(
            RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(2), Rational::integer(3))
                .is_none()
        );
        // lo >= hi rejected.
        assert!(
            RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(2), Rational::integer(1))
                .is_none()
        );
        // Endpoint that is itself a root (x²−1 at 1) rejected (open interval).
        assert!(
            RealAlgebraic::new(vec![-1, 0, 1], Rational::integer(1), Rational::integer(2))
                .is_none()
        );
    }

    #[test]
    fn sign_at_defining_poly_is_zero() {
        let a = sqrt2();
        assert_eq!(a.sign_at(&[-2, 0, 1]), Some(Sign::Zero));
        // A scalar multiple of the defining poly also vanishes (detected exactly).
        assert_eq!(a.sign_at(&[-4, 0, 2]), Some(Sign::Zero));
    }

    #[test]
    fn sign_at_linear_polys() {
        let a = sqrt2(); // +√2 ≈ 1.414
        // q = x  ⇒ positive at +√2.
        assert_eq!(a.sign_at(&[0, 1]), Some(Sign::Pos));
        // q = x − 2 ⇒ negative (√2 < 2).
        assert_eq!(a.sign_at(&[-2, 1]), Some(Sign::Neg));
        // q = x − 1 ⇒ positive (√2 > 1).
        assert_eq!(a.sign_at(&[-1, 1]), Some(Sign::Pos));
        // q = 2x − 3 ⇒ √2 ≈ 1.414, 2*1.414 − 3 = −0.17 ⇒ negative.
        assert_eq!(a.sign_at(&[-3, 2]), Some(Sign::Neg));
        // q = 5x − 7 ⇒ 5*1.414 − 7 = 0.07 ⇒ positive (needs refinement).
        assert_eq!(a.sign_at(&[-7, 5]), Some(Sign::Pos));
    }

    #[test]
    fn compare_rational_brackets() {
        let a = sqrt2();
        assert_eq!(
            a.compare_rational(&Rational::integer(1)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            a.compare_rational(&Rational::integer(2)),
            Some(Ordering::Less)
        );
        // 3/2 = 1.5 > √2.
        assert_eq!(
            a.compare_rational(&Rational::new(3, 2)),
            Some(Ordering::Less)
        );
        // 7/5 = 1.4 < √2.
        assert_eq!(
            a.compare_rational(&Rational::new(7, 5)),
            Some(Ordering::Greater)
        );
    }

    #[test]
    fn equality_same_root_overlapping_interval() {
        let a = sqrt2();
        // A tighter isolating interval for the same root.
        let b =
            RealAlgebraic::new(vec![-2, 0, 1], Rational::new(7, 5), Rational::new(3, 2)).unwrap();
        assert_eq!(a, b);
        // The other root (−√2) is a different value.
        let neg = RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(-2), Rational::integer(-1))
            .unwrap();
        assert_ne!(a, neg);
    }

    #[test]
    fn display_form() {
        let a = sqrt2();
        assert_eq!(a.to_string(), "root of 1*x^2 - 2 in (1, 2)");
    }

    /// The root-object index is the position among DISTINCT real roots, and the
    /// polynomial is canonical: the same value from a scaled defining polynomial
    /// gives the same pair.
    #[test]
    fn root_object_is_canonical_and_indexed() {
        // +sqrt(2) is the SECOND root of x^2 - 2 (the first is -sqrt(2)).
        let a = sqrt2();
        let (poly, k) = a.root_object().expect("sqrt(2) has a root object");
        assert_eq!(k, 2);
        assert_eq!(
            poly,
            vec![BigInt::from(-2), BigInt::from(0), BigInt::from(1)]
        );

        // -sqrt(2) is the FIRST root of the same polynomial.
        let neg = RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(-2), Rational::integer(-1))
            .expect("-sqrt(2) brackets");
        let (npoly, nk) = neg.root_object().expect("-sqrt(2) has a root object");
        assert_eq!(nk, 1);
        assert_eq!(npoly, poly, "the same polynomial names both roots");

        // A SCALED defining polynomial denotes the same number and must print
        // the same: 2x^2 - 4 has the same roots as x^2 - 2.
        let scaled = RealAlgebraic::new(vec![-4, 0, 2], Rational::integer(1), Rational::integer(2))
            .expect("scaled brackets");
        assert_eq!(
            scaled.root_object(),
            Some((poly.clone(), 2)),
            "content and leading sign must be normalised away"
        );

        // A NEGATED leading coefficient likewise: -x^2 + 2 has the same roots.
        let flipped =
            RealAlgebraic::new(vec![2, 0, -1], Rational::integer(1), Rational::integer(2))
                .expect("flipped brackets");
        assert_eq!(flipped.root_object(), Some((poly, 2)));
    }

    /// A polynomial with a repeated factor still indexes over DISTINCT roots,
    /// because the root object is built from the squarefree part.
    #[test]
    fn root_object_indexes_distinct_roots_of_a_repeated_factor() {
        // (x^2 - 2)^2 = x^4 - 4x^2 + 4 has the SAME two real roots, each double.
        // It has no sign change across +-sqrt(2), so it cannot bracket a root;
        // use (x^2 - 2)^2 * (x^2 - 2) = (x^2 - 2)^3, which does.
        // (x^2-2)^3 = x^6 - 6x^4 + 12x^2 - 8.
        let a = RealAlgebraic::new(
            vec![-8, 0, 12, 0, -6, 0, 1],
            Rational::integer(1),
            Rational::integer(2),
        )
        .expect("(x^2-2)^3 brackets +sqrt(2)");
        let (poly, k) = a.root_object().expect("root object");
        // Squarefree part is x^2 - 2 (up to content/sign), and +sqrt(2) is its
        // second distinct root -- NOT its sixth.
        assert_eq!(
            poly,
            vec![BigInt::from(-2), BigInt::from(0), BigInt::from(1)]
        );
        assert_eq!(k, 2);
    }

    /// Three distinct roots: the index must track position, not sign.
    ///
    /// Every bracket here is asserted to BUILD before it is asserted on -- an
    /// `if let Some` around the check would make the test pass by doing nothing.
    #[test]
    fn root_object_index_tracks_position() {
        // x^3 - 6x^2 + 11x - 6 = (x-1)(x-2)(x-3).
        let p = vec![-6, 11, -6, 1];
        for (lo, hi, want) in [
            (Rational::new(1, 2), Rational::new(3, 2), 1usize),
            (Rational::new(3, 2), Rational::new(5, 2), 2),
            (Rational::new(5, 2), Rational::new(7, 2), 3),
        ] {
            let r = RealAlgebraic::new(p.clone(), lo, hi)
                .expect("each bracket straddles exactly one root of (x-1)(x-2)(x-3)");
            assert_eq!(
                r.root_object().map(|(_, k)| k),
                Some(want),
                "root in ({lo}, {hi}) must be number {want}"
            );
        }
    }

    /// **Regression (ADR-2134).** Two roots of `q` inside the isolating bracket.
    ///
    /// `alpha = sqrt(2) ~ 1.41421` is bracketed by `(1, 2)`.
    /// `q = 25x^2 - 70x + 48 = (5x - 6)(5x - 8)` has roots `1.2` and `1.6`, so it
    /// is POSITIVE at both endpoints (`q(1) = 3`, `q(2) = 8`) and NEGATIVE at
    /// `alpha` (`q(sqrt 2) ~ -0.995`).
    ///
    /// Reading the two endpoint signs alone answers `Pos` here -- a WRONG sign in
    /// the trusted evaluation path. The exact side condition (`q` has no root
    /// strictly inside the bracket) is what rejects that read and forces
    /// refinement until the bracket separates from both roots.
    ///
    /// This shape is unreachable by `sign_at_matches_float_oracle`: that sweep
    /// runs `c0, c1 in -5..=5` and `c2 in -3..=3`, and the constraints
    /// `q(1) > 0`, `q(2) > 0`, `q(sqrt 2) < 0` have NO integer solution in that
    /// box (they force `c1 < -4.83` together with a `c0` in an interval of width
    /// `< 0.08`). A blind population that cannot contain the defect measures the
    /// subset it happens to cover.
    #[test]
    fn regression_two_roots_inside_the_bracket() {
        let a = sqrt2();
        // q = 25x^2 - 70x + 48, LSB-first.
        let q = [48, -70, 25];
        // Both endpoints of the isolating bracket are POSITIVE -- the trap.
        assert_eq!(
            big_sign(&big_eval_int_at(
                &bigint_poly_from_i128(&q),
                &bigrational_from_i128(1, 1)
            )),
            Sign::Pos,
            "q(1) must be positive for this fixture to be the trap it claims"
        );
        assert_eq!(
            big_sign(&big_eval_int_at(
                &bigint_poly_from_i128(&q),
                &bigrational_from_i128(2, 1)
            )),
            Sign::Pos,
            "q(2) must be positive for this fixture to be the trap it claims"
        );
        // The true sign at sqrt(2) is NEGATIVE.
        assert_eq!(a.sign_at(&q), Some(Sign::Neg));
        // ... and negating q flips it, so the answer is not a constant.
        assert_eq!(a.sign_at(&[-48, 70, -25]), Some(Sign::Pos));
    }

    /// The same trap as a FAMILY rather than one point: every quadratic whose two
    /// rational roots straddle `sqrt(2)` strictly inside the bracket `(1, 2)`.
    ///
    /// `q(x) = (d*x - n1)(d*x - n2)` with `n1/d < sqrt 2 < n2/d` is positive at
    /// both endpoints and negative at `alpha`. The oracle here is ALGEBRAIC, not
    /// floating point: a product of two linear factors is negative exactly
    /// between its roots, and `n1/d < sqrt 2 < n2/d` is decided exactly by
    /// comparing `n^2` against `2 d^2`.
    #[test]
    fn sign_at_two_roots_straddling_alpha_family() {
        let a = sqrt2();
        let mut checked = 0usize;
        for d in 2..=12i128 {
            for n1 in 1..(2 * d) {
                for n2 in (n1 + 1)..(2 * d) {
                    // Strictly inside (1, 2): d < n < 2d.
                    if n1 <= d || n2 <= d {
                        continue;
                    }
                    // n1/d < sqrt 2 < n2/d, exactly.
                    if !(n1 * n1 < 2 * d * d && n2 * n2 > 2 * d * d) {
                        continue;
                    }
                    // q = (d x - n1)(d x - n2) = d^2 x^2 - d(n1+n2) x + n1 n2.
                    let q = [n1 * n2, -d * (n1 + n2), d * d];
                    assert_eq!(
                        a.sign_at(&q),
                        Some(Sign::Neg),
                        "q=(({d}x-{n1})({d}x-{n2})) is negative at sqrt(2)"
                    );
                    // The negation must flip, never agree.
                    assert_eq!(
                        a.sign_at(&[-(n1 * n2), d * (n1 + n2), -(d * d)]),
                        Some(Sign::Pos),
                        "negated q must be positive at sqrt(2)"
                    );
                    checked += 1;
                }
            }
        }
        // The population must be non-empty: an adversarial family that generates
        // nothing is a test that cannot fail.
        assert!(
            checked >= 20,
            "the straddling family must be non-trivial, got {checked}"
        );
    }

    /// The side condition is a SIDE condition, not the answer: a polynomial with
    /// no root in the bracket still resolves on the first read, so the fix does
    /// not turn ordinary sign queries into declines.
    #[test]
    fn sign_at_still_resolves_when_no_root_is_inside() {
        let a = sqrt2();
        // (x - 5): root at 5, far outside (1, 2).
        assert_eq!(a.sign_at(&[-5, 1]), Some(Sign::Neg));
        // (x^2 - 9): roots at +-3, outside (1, 2).
        assert_eq!(a.sign_at(&[-9, 0, 1]), Some(Sign::Neg));
        // A nonzero constant has no roots anywhere.
        assert_eq!(a.sign_at(&[7]), Some(Sign::Pos));
        assert_eq!(a.sign_at(&[-7]), Some(Sign::Neg));
    }

    /// Property: `sign_at` agrees with a brute-force floating-point oracle on a
    /// batch of small polynomials. FLOAT IS USED ONLY IN THIS TEST ORACLE, never
    /// in the implementation under test.
    #[test]
    fn sign_at_matches_float_oracle() {
        // α = √2, the positive root of x²−2, ≈ 1.4142135623730951.
        let a = sqrt2();
        let alpha = 2.0f64.sqrt();
        // Sweep q = c1*x + c0 and a few quadratics with small integer coeffs.
        for c0 in -5..=5i128 {
            for c1 in -5..=5i128 {
                for c2 in -3..=3i128 {
                    let q = vec![c0, c1, c2];
                    // Float oracle value of q(α).
                    #[allow(clippy::cast_precision_loss)]
                    let fval = (c0 as f64) + (c1 as f64) * alpha + (c2 as f64) * alpha * alpha;
                    let got = a.sign_at(&q);
                    // Skip near-zero oracle values: the float oracle cannot
                    // reliably distinguish sign there, and `sign_at` may return
                    // Zero only for genuine algebraic vanishing (e.g. q ∝ x²−2).
                    if fval.abs() < 1e-9 {
                        // Must be Zero or a definite sign; just require it not crash.
                        assert!(got.is_some(), "sign_at must decide q={q:?}");
                        continue;
                    }
                    let want = if fval < 0.0 { Sign::Neg } else { Sign::Pos };
                    assert_eq!(got, Some(want), "q={q:?} α=√2 fval={fval}");
                }
            }
        }
    }
}
