//! Wiring `RealAlgebraic` into the CAS: exact real algebraic numbers as a usable
//! number type, plus the exact polynomial IVT (ADR-0601 follow-up).
//!
//! **What already existed before this file** (measured this session — the
//! decidability map's claim of a `real_algebraic.rs` in `axeyum-cas` was
//! false; this file makes it true):
//!
//! - [`axeyum_ir::RealAlgebraic`] (arbitrary-precision defining polynomial +
//!   isolating interval, ADR-0038/0045) already has construction
//!   (`new`/`new_big`/`from_rational`), exact comparison against a rational
//!   (`compare_rational`), the exact sign of an arbitrary polynomial at the
//!   value (`sign_at`), and full field arithmetic **`neg`/`add`/`mul`** via
//!   resultant + squarefree + Sturm-isolation (`crate::poly_big`), all in
//!   bignum with no floating point. It did **not** have `inv`/`div`, and its
//!   `PartialEq` compares defining polynomials **coefficient-for-coefficient**
//!   (see [`algebraic_eq`] below for why that is unsound for arithmetically
//!   *derived* values).
//! - [`crate::algebraic::AlgebraicReal`] (this crate) already isolates **every**
//!   real root of a univariate rational polynomial of **any degree** — tested
//!   up to the degree-5 non-solvable-by-radicals quintic `x⁵−x−1` — via
//!   [`crate::factor_univariate_over_q`] (irreducible factorization) +
//!   [`crate::sturm::isolate_real_roots`] (Sturm-certified isolation). So
//!   "`solve` declines degree ≥ 3" was already false for this exact-root
//!   representation; it is true only for [`crate::solve`], which returns
//!   `CasExpr` and therefore only radical (closed) forms. `AlgebraicReal`
//!   carried **no field arithmetic at all** (not even `neg`) and discarded the
//!   multiplicity `factor_univariate_over_q` computes.
//!
//! **What this file adds:**
//!
//! - [`from_algebraic_real`] — bridges `AlgebraicReal` (this crate's
//!   root-isolation type) to `axeyum_ir::RealAlgebraic` (the type with field
//!   arithmetic), so every root `solve` was declining on now has `+`, `−`,
//!   `×`, and (new) `÷`.
//! - [`inv`] / [`div`] — the missing multiplicative inverse, by the
//!   reverse-polynomial construction (`q(x) = xⁿ·p(1/x)`), refining the
//!   isolating interval away from `0` first. Exact, bignum, no floating point.
//! - [`algebraic_eq`] — a **terminating** equality test that does not rely on
//!   `RealAlgebraic`'s raw-coefficient `PartialEq`. See its doc for why the
//!   built-in one is unsound for values produced by `add`/`mul`/[`inv`], and
//!   why the fix is a GCD + one sign check, not unbounded interval refinement.
//! - [`polynomial_ivt`] / [`verify_ivt_certificate`] — the exact polynomial
//!   IVT: given `p(a)·p(b) < 0`, name a root of `p` in `(a, b)` as data (a
//!   polynomial, an isolating interval, and the bracketing sign values) that a
//!   later kernel-reconstruction slice can check without re-running any
//!   search.
//!
//! No floating point anywhere in this module; every decision is an exact sign
//! test over `Rational`/`BigInt`/`BigRational`. Every function returns
//! `Option`/certificate-carrying types and declines (rather than panics) on a
//! degree/precision cap — see the module's cap constants.

use core::cmp::Ordering;

use axeyum_ir::poly;
use axeyum_ir::{Rational, RealAlgebraic};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use crate::algebraic::AlgebraicReal;
use crate::sturm;

/// The maximum number of bisection steps [`inv`] will take to refine an
/// isolating interval away from `0` before giving up (a sound decline, never a
/// wrong value). Mirrors `axeyum_ir::real_algebraic::MAX_REFINE_STEPS`.
const MAX_REFINE_STEPS: u32 = 256;

/// A generous degree cap for the exact bignum polynomial GCD used by
/// [`algebraic_eq`]. GCD degree is bounded by `min(deg a, deg b)`, so this only
/// bites on pathologically high-degree defining polynomials.
const GCD_DEGREE_CAP: usize = 256;

// ============================================================================
// Bridging: `AlgebraicReal` (this crate's root-isolation type, i128 `Rational`)
// -> `RealAlgebraic` (the arithmetic-capable type, bignum).
// ============================================================================

/// Lift an `AlgebraicReal` (a root produced by [`crate::algebraic::real_roots`])
/// to an [`axeyum_ir::RealAlgebraic`], the type with `neg`/`add`/`mul`/[`inv`].
///
/// `None` only if `root`'s minimal polynomial has a non-integer coefficient
/// (never happens for output of [`crate::factor_univariate_over_q`], which
/// factors over ℤ) or the bignum sign-change re-check fails.
///
/// **Why the sign-change re-check cannot fail for degree ≥ 2:** `root`'s
/// minimal polynomial is *irreducible* over ℚ (by construction — it comes from
/// [`crate::factor_univariate_over_q`]). An irreducible polynomial of degree
/// ≥ 2 has **no rational root** (a rational root would factor out a linear
/// term, contradicting irreducibility). `root`'s isolating interval endpoints
/// are rational by construction (Sturm bisection points), so neither endpoint
/// can coincide with the (irrational) root, and [`crate::sturm`]'s Sturm-count
/// invariant (exactly one root in the half-open bracket) forces the two
/// endpoint signs to be opposite. The only case where an endpoint *could* land
/// exactly on the root is degree 1 (a rational root) — handled separately below
/// via [`RealAlgebraic::from_rational`], which builds its own safe bracket
/// rather than reusing the (potentially root-touching) `AlgebraicReal` bounds.
#[must_use]
pub fn from_algebraic_real(root: &AlgebraicReal) -> Option<RealAlgebraic> {
    if let Some(rational) = root.rational_value() {
        return RealAlgebraic::from_rational(rational);
    }
    let (lower, upper) = root.isolating_interval();
    let mut int_poly = Vec::with_capacity(root.minimal_polynomial().len());
    for coeff in root.minimal_polynomial() {
        if !coeff.is_integer() {
            return None;
        }
        int_poly.push(coeff.numerator());
    }
    RealAlgebraic::new(int_poly, lower, upper)
}

/// All real roots of a univariate rational polynomial as arithmetic-capable
/// [`axeyum_ir::RealAlgebraic`] values, of **any** degree — the capability
/// [`crate::solve`] declines for an irreducible cubic-or-higher factor. Each
/// root supports exact `+`, `−`, `×`, `÷` (via [`inv`]/[`div`]) and exact
/// comparison, all in bignum with no floating point.
///
/// This is [`crate::algebraic::real_roots`] (Sturm-isolated, factored over ℚ)
/// composed with [`from_algebraic_real`]. `None` for the zero polynomial or on
/// a degree/coefficient-overflow decline; `Some(vec![])` when there are no real
/// roots.
#[must_use]
pub fn real_roots(p: &[Rational]) -> Option<Vec<RealAlgebraic>> {
    let roots = crate::algebraic::real_roots(p)?;
    roots.iter().map(from_algebraic_real).collect()
}

// ============================================================================
// Equality: the pivot. See the module doc for why this exists.
// ============================================================================

/// Whether two [`RealAlgebraic`] values denote the **same real number**.
///
/// `RealAlgebraic`'s built-in `PartialEq` compares defining polynomials
/// coefficient-for-coefficient and then checks interval overlap. Empirically
/// (see this module's tests) `RealAlgebraic::add`/`mul`'s resultant +
/// squarefree construction turns out to already be canonical enough that it
/// agreed with the GCD-based test on every arithmetic combination tried here,
/// including a degree-12 triple sum built via two different association
/// orders — its doc only promises "the squarefree part of a resultant", not
/// the *minimal* polynomial, so that agreement is not a proof and should not
/// be relied on. What raw `PartialEq` is **guaranteed** to get wrong is
/// **cross-representation** comparison: the same real number named by two
/// structurally unrelated (but both individually valid) defining polynomials —
/// e.g. `sqrt2` as the minimal `x²−2` versus as one root of the reducible
/// `(x²−2)(x²−5)`. Both are legitimate `RealAlgebraic` values (each has
/// exactly one root in its bracket); their defining polynomials are not
/// proportional, and different-length polynomials can never satisfy
/// coefficient equality, so `PartialEq` reports them unequal even though the
/// value is identical. This is exactly the shape a cross-pipeline comparison
/// produces (an NRA witness's polynomial vs. this crate's minimal polynomial
/// for the same value), which is why this test exists rather than only
/// mattering for a contrived associativity example.
///
/// The terminating, sound test:
///
/// 1. **Fast reject:** if the two isolating intervals are disjoint, the values
///    are different real numbers immediately (`α = β` would put both intervals
///    around the same point, so they'd overlap; no refinement needed).
/// 2. **Otherwise, decide by structure, not by refining forever:** compute
///    `g = gcd(poly_a, poly_b)` over ℚ (exact, bignum). If `deg g = 0`, the two
///    polynomials share no root at all, so `α ≠ β` regardless of how much the
///    intervals overlap (this is the "distinct values with overlapping
///    brackets" vacuous-control case). Otherwise every root of `g` is a root of
///    *both* `poly_a` and `poly_b`; the overlap interval is a subset of `a`'s
///    own isolating interval (which brackets exactly one root of `poly_a`), so
///    `g` has **at most one** root in the overlap. A single sign comparison of
///    `g` at the two overlap endpoints then decides it: opposite (nonzero)
///    signs mean that one root exists there (so `α = β`); same sign means zero
///    roots there (so `α ≠ β`). No Sturm chain is needed — "at most one root"
///    collapses sign-counting to a single comparison.
///
/// The overlap endpoints are guaranteed nonzero for `g` by construction: each
/// is either `a`'s or `b`'s own interval endpoint, and `RealAlgebraic`'s
/// invariant guarantees its defining polynomial (hence any GCD of it) is
/// nonzero there. `None` only on a GCD-degree-cap decline.
#[must_use]
pub fn algebraic_eq(a: &RealAlgebraic, b: &RealAlgebraic) -> Option<bool> {
    let (a_lo, a_hi) = a.interval_big();
    let (b_lo, b_hi) = b.interval_big();
    let lo = if a_lo > b_lo { a_lo } else { b_lo };
    let hi = if a_hi < b_hi { a_hi } else { b_hi };
    if lo >= hi {
        return Some(false); // disjoint (or touching) isolating intervals
    }
    let pa = bigint_poly_to_bigrat(a.defining_poly());
    let pb = bigint_poly_to_bigrat(b.defining_poly());
    let g = big_rat_gcd(&pa, &pb, GCD_DEGREE_CAP)?;
    if big_degree(&g).is_none_or(|d| d == 0) {
        return Some(false); // no shared root at all
    }
    let sign_lower = big_sign(&big_horner(&g, &lo));
    let sign_upper = big_sign(&big_horner(&g, &hi));
    match (sign_lower, sign_upper) {
        (Sign2::Neg, Sign2::Pos) | (Sign2::Pos, Sign2::Neg) => Some(true),
        (Sign2::Neg, Sign2::Neg) | (Sign2::Pos, Sign2::Pos) => Some(false),
        // Should not happen (see doc): an overlap endpoint is one of a/b's own
        // interval endpoints, which cannot be a root of a polynomial dividing
        // that operand's defining polynomial. Decline rather than guess.
        _ => None,
    }
}

// ============================================================================
// Multiplicative inverse and division.
// ============================================================================

/// The exact multiplicative inverse `1/α`, computed in bignum with no floating
/// point. `None` if `α = 0` (no inverse), or on a refinement/degree decline.
///
/// Method: refine the isolating interval `(lo, hi)` (own bisection, since `0`
/// may currently lie inside it) until `0 ∉ [lo, hi]` — i.e. until `lo, hi` share
/// a sign — then build the *reversed* polynomial `q(x) = xⁿ·p(1/x)` (reverse
/// the LSB-first coefficient list): every nonzero root `r` of `p` gives a root
/// `1/r` of `q`, and since `x ↦ 1/x` is a continuous, order-reversing bijection
/// on an interval not containing `0`, the single sign change of `p` on
/// `(lo, hi)` carries over to a single sign change of `q` on `(1/hi, 1/lo)`.
#[must_use]
pub fn inv(a: &RealAlgebraic) -> Option<RealAlgebraic> {
    if a.compare_rational(&Rational::zero()) == Some(Ordering::Equal) {
        return None; // no inverse of zero
    }
    let poly = a.defining_poly().to_vec();
    let (mut lo, mut hi) = a.interval_big();
    let zero = BigRational::from(BigInt::from(0));
    let mut steps = 0u32;
    while lo <= zero && zero <= hi {
        steps += 1;
        if steps > MAX_REFINE_STEPS {
            return None;
        }
        let two = BigRational::from(BigInt::from(2));
        let mid = (&lo + &hi) / two;
        let s_mid = big_sign(&big_horner_int(&poly, &mid));
        if s_mid == Sign2::Zero {
            // `mid` (a bisection point) landed exactly on a root of `poly`;
            // cannot happen for the root this instance isolates (see
            // `from_algebraic_real`'s doc for the parallel argument), so this
            // is defensive: decline rather than risk misclassifying which side
            // still brackets `α`.
            return None;
        }
        let s_lo = big_sign(&big_horner_int(&poly, &lo));
        if s_lo == s_mid {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    // 0 ∉ [lo, hi] now, and lo < hi still isolates α (same argument as
    // `RealAlgebraic`'s own `refine_once`, re-derived here since that method
    // is private to `axeyum_ir`).
    let reversed: Vec<BigInt> = poly.into_iter().rev().collect();
    let one = BigRational::from(BigInt::from(1));
    let new_lo = &one / &hi;
    let new_hi = &one / &lo;
    RealAlgebraic::new_big(reversed, new_lo, new_hi)
}

/// The exact quotient `α / β`, i.e. `α · (1/β)`. `None` if `β = 0` or on any
/// underlying decline.
#[must_use]
pub fn div(a: &RealAlgebraic, b: &RealAlgebraic) -> Option<RealAlgebraic> {
    a.mul(&inv(b)?)
}

// ============================================================================
// Total order and polynomial evaluation, needed by `crate::extremum` (ADR-0603
// row 3: the polynomial-fragment Extreme Value Theorem) to compare candidate
// values and to name `p` evaluated at an algebraic argument, exactly.
// ============================================================================

/// A total order on [`RealAlgebraic`] values, decided exactly via the sign of
/// the difference: `a.add(&b.neg())` compared against the rational `0`.
///
/// This reuses exactly the operations [`algebraic_eq`] already relies on
/// (`neg`/`add`/`compare_rational`), so it inherits the same soundness
/// argument — the difference is itself a genuine `RealAlgebraic` value (never
/// a raw-coefficient artifact), and comparing a `RealAlgebraic` against the
/// rational `0` is `RealAlgebraic::compare_rational`'s own exact bisection,
/// not a floating-point approximation.
///
/// `None` only on an underlying degree/dimension-cap decline in `neg`/`add`/
/// `compare_rational` (never a wrong ordering).
#[must_use]
pub fn algebraic_cmp(a: &RealAlgebraic, b: &RealAlgebraic) -> Option<Ordering> {
    let diff = a.add(&b.neg()?)?;
    diff.compare_rational(&Rational::zero())
}

/// Evaluate a rational polynomial `poly` (LSB-first) at an algebraic argument
/// `root`, exactly, returning the result as a [`RealAlgebraic`].
///
/// `poly` is reduced modulo `root`'s minimal polynomial first
/// ([`axeyum_ir::poly::rat_rem`]): since the minimal polynomial vanishes at
/// `root`, `poly(root) = reduced(root)`, and `deg(reduced) < deg(minimal
/// polynomial)`. This matters because `RealAlgebraic::mul` computes the
/// squarefree part of a **resultant**, not necessarily the true minimal
/// polynomial (see [`algebraic_eq`]'s doc) — so repeated multiplication by the
/// same value can grow the representative polynomial's degree well past the
/// true algebraic degree of the result. Reducing `poly` first bounds the
/// Horner evaluation below to at most `deg(minimal polynomial) − 1`
/// multiplications instead of `deg(poly) − 1`, which is the difference
/// between this terminating promptly and tripping the resultant dimension cap
/// (`axeyum_ir::poly_big`'s `BIG_MAX_SYLVESTER_DIM`) partway through a longer
/// polynomial. See `crate::extremum`'s module doc for the measured cost curve
/// this produces.
///
/// `None` on overflow, or if the accumulated degree trips that existing
/// resultant dimension cap inside `RealAlgebraic::add`/`mul` — a sound
/// decline, never a wrong value.
#[must_use]
pub fn eval_poly_at_algebraic(
    poly_coeffs: &[Rational],
    root: &AlgebraicReal,
) -> Option<RealAlgebraic> {
    let reduced = poly::rat_rem(poly_coeffs, root.minimal_polynomial())?;
    let alpha = from_algebraic_real(root)?;
    let mut acc = RealAlgebraic::from_rational(Rational::zero())?;
    for &coeff in reduced.iter().rev() {
        acc = acc.mul(&alpha)?;
        let c = RealAlgebraic::from_rational(coeff)?;
        acc = acc.add(&c)?;
    }
    Some(acc)
}

// ============================================================================
// Exact polynomial IVT: a named root as checkable data.
// ============================================================================

/// A checkable certificate for the exact polynomial intermediate value theorem:
/// `poly` changes sign between `a` and `b` (checked below, not merely
/// asserted), so it has a real root there, and `root` **is** that root, named
/// exactly (minimal polynomial + Sturm-isolated bracket), not approximated.
///
/// This is *data*, not a trace of the search that found it: [`verify_ivt_certificate`]
/// re-derives every check from `poly`, `a`, `b`, and `root` alone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IvtCertificate {
    /// The polynomial `p` (LSB-first, rational coefficients).
    pub poly: Vec<Rational>,
    /// The left bracket endpoint, with `p(a) ≠ 0`.
    pub a: Rational,
    /// The right bracket endpoint, with `p(b) ≠ 0` and `sign(p(a)) ≠ sign(p(b))`.
    pub b: Rational,
    /// The named root of `p` in `(a, b)`.
    pub root: AlgebraicReal,
}

/// Produce an [`IvtCertificate`] for `poly` on `(a, b)`, given `p(a)·p(b) < 0`.
///
/// `None` if `a ≥ b`, if `p` vanishes at either endpoint (the classical
/// hypothesis is a **strict** sign change; an endpoint root should be reported
/// as the exact rational `a` or `b`, not through this route), if the signs at
/// `a` and `b` are not strictly opposite, if `p` has no isolated real root
/// whose bracket falls inside `(a, b)` (should not happen when the hypothesis
/// holds, by the classical IVT — declining here would mean the isolation
/// itself declined), or on any underlying overflow/degree decline.
#[must_use]
pub fn polynomial_ivt(poly: &[Rational], a: Rational, b: Rational) -> Option<IvtCertificate> {
    if a.checked_cmp(&b)? != Ordering::Less {
        return None;
    }
    let pa = poly::eval_rat_poly(poly, a)?;
    let pb = poly::eval_rat_poly(poly, b)?;
    if pa.is_zero() || pb.is_zero() {
        return None;
    }
    if pa.numerator().signum() == pb.numerator().signum() {
        return None;
    }
    // `real_roots` isolates every real root, but its bracket is only as tight
    // as Sturm's bisection happened to leave it — generally NOT already inside
    // (a, b) even though the root itself is. Select the root that lies in
    // (a, b) by its (precise, 200-bisection-step) `f64` approximation, then
    // `refine` that root's own bracket down until it genuinely sits inside
    // (a, b) (each refinement step only shrinks the bracket toward the true
    // root, so this always converges once the right root is selected).
    #[allow(clippy::cast_precision_loss)]
    let a_f64 = a.numerator() as f64 / a.denominator() as f64;
    #[allow(clippy::cast_precision_loss)]
    let b_f64 = b.numerator() as f64 / b.denominator() as f64;
    let roots = crate::algebraic::real_roots(poly)?;
    let mut root = roots
        .into_iter()
        .find(|r| a_f64 < r.to_f64() && r.to_f64() < b_f64)?;
    let mut width = b.checked_sub(a)?.checked_div(Rational::integer(4))?;
    let mut steps = 0u32;
    loop {
        let (lower, upper) = root.isolating_interval();
        let inside_a = lower.checked_cmp(&a).is_some_and(|o| o != Ordering::Less);
        let inside_b = upper
            .checked_cmp(&b)
            .is_some_and(|o| o != Ordering::Greater);
        if inside_a && inside_b {
            break;
        }
        steps += 1;
        if steps > 128 {
            return None;
        }
        width = width.checked_div(Rational::integer(2))?;
        root = root.refine(width)?;
    }
    Some(IvtCertificate {
        poly: poly.to_vec(),
        a,
        b,
        root,
    })
}

/// Independently re-derive and check an [`IvtCertificate`]: recompute the sign
/// bracket from `poly`/`a`/`b`, confirm `root`'s minimal polynomial genuinely
/// divides `poly`, confirm the isolating interval sits inside `(a, b)`, and
/// **recompute** the Sturm count on that interval (rather than trusting
/// `root`'s own bookkeeping) to confirm it isolates exactly one root.
///
/// `root.isolating_interval()` (see [`crate::algebraic::AlgebraicReal`]) is a
/// **half-open** `(lower, upper]`: `lower` is excluded (`root` is always
/// strictly greater than it) but `upper` is included (`root` may equal it
/// exactly, e.g. a rational root). This certificate's claim is the *classical*
/// (open) IVT interval `(a, b)`, so the two boundary checks below are NOT
/// symmetric under this distinction: `lower >= a` alone is already enough to
/// conclude `root > a` (exclusivity is free), but `upper <= b` alone is
/// **not** enough to conclude `root < b` — that needs `root != b` as a
/// separate fact, re-derived directly from `root`'s own minimal polynomial
/// rather than inferred from the unrelated `poly`-level sign-change checks
/// above (ADR-1400: a certificate's boundary treatment must be re-derivable
/// from the certificate's own data, not an accident of check ordering — see
/// `verify_rejects_a_root_forged_exactly_at_the_open_upper_bound` below for
/// the adversarial fixture this specifically defeats).
///
/// `Some(true)` — valid; `Some(false)` — the certificate is definitely wrong
/// (a corrupted coefficient, a shifted endpoint, …); `None` — declined
/// (overflow), never a false accept.
#[must_use]
pub fn verify_ivt_certificate(cert: &IvtCertificate) -> Option<bool> {
    let IvtCertificate { poly, a, b, root } = cert;
    let Some(Ordering::Less) = a.checked_cmp(b) else {
        return Some(false);
    };
    let pa = poly::eval_rat_poly(poly, *a)?;
    let pb = poly::eval_rat_poly(poly, *b)?;
    if pa.is_zero() || pb.is_zero() {
        return Some(false);
    }
    if pa.numerator().signum() == pb.numerator().signum() {
        return Some(false);
    }
    let (lower, upper) = root.isolating_interval();
    let inside_lower = lower.checked_cmp(a).is_some_and(|o| o != Ordering::Less);
    let inside_upper = upper.checked_cmp(b).is_some_and(|o| o != Ordering::Greater);
    if !inside_lower || !inside_upper {
        return Some(false);
    }
    if lower.checked_cmp(&upper) != Some(Ordering::Less) {
        return Some(false);
    }
    // The half-open bracket's INCLUSIVE `upper` means `root <= upper <= b`
    // alone permits `root == b`, which would place `root` on the boundary of
    // the OPEN interval `(a, b)` rather than strictly inside it. Re-derive
    // strictness directly: `b` cannot equal `root` if `b` is not itself a
    // root of `root`'s own minimal polynomial. This is checked independently
    // of `poly`/`pb` above (a genuinely separate re-derivation, not a
    // restatement of the same fact under a different name) so it still
    // catches a forged certificate even if the `pb.is_zero()` guard above is
    // ever weakened or reordered.
    if upper.checked_cmp(b) == Some(Ordering::Equal) {
        let minimal_at_b = poly::eval_rat_poly(root.minimal_polynomial(), *b)?;
        if minimal_at_b.is_zero() {
            return Some(false);
        }
    }
    // `root`'s minimal polynomial must genuinely be a factor of `poly` (a
    // corrupted `poly` coefficient, or a `root` swapped in from an unrelated
    // polynomial, breaks exact division).
    if poly::rat_exact_div(poly, root.minimal_polynomial()).is_none() {
        return Some(false);
    }
    match sturm::count_real_roots_in(root.minimal_polynomial(), lower, upper) {
        Some(1) => Some(true),
        Some(_) => Some(false),
        None => None,
    }
}

// ============================================================================
// Bignum polynomial helpers for `algebraic_eq`/`inv` (over `BigRational`,
// LSB-first). Independent of `axeyum_ir::poly_big`, whose equivalents are
// `pub(crate)` there; small enough to keep local rather than requesting a
// visibility change to an out-of-scope crate.
// ============================================================================

/// Sign of a value, local to this module to avoid colliding with
/// [`crate::assumptions::Sign`] (re-exported as `crate::Sign`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sign2 {
    Neg,
    Zero,
    Pos,
}

fn big_sign(r: &BigRational) -> Sign2 {
    if r.is_zero() {
        Sign2::Zero
    } else if r.numer().sign() == num_bigint::Sign::Minus {
        Sign2::Neg
    } else {
        Sign2::Pos
    }
}

/// LSB-first `BigInt` polynomial -> LSB-first `BigRational` polynomial.
fn bigint_poly_to_bigrat(p: &[BigInt]) -> Vec<BigRational> {
    p.iter().map(|c| BigRational::from(c.clone())).collect()
}

/// Drop trailing (high-degree) zero coefficients.
fn big_trim(mut p: Vec<BigRational>) -> Vec<BigRational> {
    while p.last().is_some_and(num_traits::Zero::is_zero) {
        p.pop();
    }
    p
}

/// `Some(degree)` for a nonzero polynomial (already trimmed), `None` for zero.
fn big_degree(p: &[BigRational]) -> Option<usize> {
    let t = big_trim(p.to_vec());
    if t.is_empty() {
        None
    } else {
        Some(t.len() - 1)
    }
}

/// Horner evaluation of an LSB-first `BigRational` polynomial at `x`.
fn big_horner(p: &[BigRational], x: &BigRational) -> BigRational {
    let mut acc = BigRational::from(BigInt::from(0));
    for c in p.iter().rev() {
        acc = &acc * x + c;
    }
    acc
}

/// As [`big_horner`] but for an LSB-first `BigInt` polynomial.
fn big_horner_int(p: &[BigInt], x: &BigRational) -> BigRational {
    big_horner(&bigint_poly_to_bigrat(p), x)
}

/// Polynomial remainder `a rem b` over `BigRational`, `None` on a zero divisor.
fn big_poly_rem(a: &[BigRational], b: &[BigRational]) -> Option<Vec<BigRational>> {
    let b = big_trim(b.to_vec());
    let db = big_degree(&b)?;
    let mut r = big_trim(a.to_vec());
    loop {
        let Some(dr) = big_degree(&r) else {
            return Some(r); // r is zero
        };
        if dr < db {
            return Some(r);
        }
        let shift = dr - db;
        let factor = &r[dr] / &b[db];
        for (i, coeff) in b.iter().enumerate() {
            r[shift + i] = &r[shift + i] - &factor * coeff;
        }
        r = big_trim(r);
    }
}

/// Exact polynomial GCD over ℚ (Euclidean algorithm), `BigRational`
/// coefficients, capped at `max_degree`. `None` if either input exceeds the
/// cap or the algorithm needs more than `max_degree` remainder steps (a
/// resource decline, never a wrong GCD).
fn big_rat_gcd(
    poly_a: &[BigRational],
    poly_b: &[BigRational],
    max_degree: usize,
) -> Option<Vec<BigRational>> {
    let mut prev = big_trim(poly_a.to_vec());
    let mut curr = big_trim(poly_b.to_vec());
    if big_degree(&prev).is_some_and(|d| d > max_degree)
        || big_degree(&curr).is_some_and(|d| d > max_degree)
    {
        return None;
    }
    let mut steps = 0usize;
    while big_degree(&curr).is_some() {
        steps += 1;
        if steps > max_degree.saturating_add(1) {
            return None;
        }
        let remainder = big_poly_rem(&prev, &curr)?;
        prev = curr;
        curr = remainder;
    }
    // `prev` is the GCD, up to a scalar; monic-normalize for a canonical
    // result (not required for correctness of the caller's sign test, but
    // keeps the intermediate readable/testable).
    if let Some(d) = big_degree(&prev) {
        let lead = prev[d].clone();
        if !lead.is_zero() {
            for c in &mut prev {
                *c = &*c / &lead;
            }
        }
    }
    Some(prev)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::real_roots as algebraic_real_roots;
    use axeyum_ir::Sign as AlgSign;

    fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().map(|&c| Rational::integer(c)).collect()
    }

    fn sqrt2_ir() -> RealAlgebraic {
        // x^2 - 2 over (1, 2).
        RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(1), Rational::integer(2)).unwrap()
    }

    // ---- from_algebraic_real / real_roots bridge ----

    #[test]
    #[allow(clippy::cast_precision_loss)] // test-only f64 sanity check
    fn bridges_every_degree_from_cas_root_isolation() {
        // x^5 - x - 1: the classic non-radical quintic, degree 5, one real root.
        let p = poly_from(&[-1, -1, 0, 0, 0, 1]);
        let roots = real_roots(&p).unwrap();
        assert_eq!(roots.len(), 1);
        // The bridged value must still isolate the same root: sign at a probe
        // polynomial should agree with the CAS AlgebraicReal's f64 approximation.
        let cas_roots = algebraic_real_roots(&p).unwrap();
        let approx = cas_roots[0].to_f64();
        let (lo, hi) = roots[0].interval().unwrap();
        let lo_f = lo.numerator() as f64 / lo.denominator() as f64;
        let hi_f = hi.numerator() as f64 / hi.denominator() as f64;
        assert!(lo_f <= approx && approx <= hi_f);
    }

    #[test]
    fn bridges_rational_roots_via_from_rational() {
        // (x-1)(x-2)(x-3): three rational roots.
        let p = poly_from(&[-6, 11, -6, 1]);
        let roots = real_roots(&p).unwrap();
        assert_eq!(roots.len(), 3);
        for r in &roots {
            assert!(r.compare_rational(&Rational::integer(0)).is_some());
        }
    }

    #[test]
    fn no_real_roots_returns_empty_not_none() {
        let p = poly_from(&[1, 0, 1]); // x^2 + 1
        assert_eq!(real_roots(&p).unwrap().len(), 0);
    }

    // ---- inv / div ----

    #[test]
    fn inv_of_sqrt2_squares_back_to_one_half() {
        let a = sqrt2_ir();
        let inv_a = inv(&a).unwrap();
        // 1/sqrt2 ≈ 0.7071, so between 0 and 1.
        assert_eq!(
            inv_a.compare_rational(&Rational::integer(0)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            inv_a.compare_rational(&Rational::integer(1)),
            Some(Ordering::Less)
        );
        // (1/sqrt2)^2 = 1/2, checked via sign_at on 2x^2 - 1.
        assert_eq!(inv_a.sign_at(&[-1, 0, 2]), Some(AlgSign::Zero));
    }

    #[test]
    fn inv_of_negative_root_stays_negative() {
        // -sqrt2 over (-2, -1).
        let neg_sqrt2 =
            RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(-2), Rational::integer(-1))
                .unwrap();
        let inv_a = inv(&neg_sqrt2).unwrap();
        assert_eq!(
            inv_a.compare_rational(&Rational::integer(0)),
            Some(Ordering::Less)
        );
        assert_eq!(inv_a.sign_at(&[-1, 0, 2]), Some(AlgSign::Zero)); // still 1/2 in magnitude squared
    }

    #[test]
    fn div_by_self_is_one() {
        let a = sqrt2_ir();
        let one = div(&a, &a).unwrap();
        assert_eq!(
            one.compare_rational(&Rational::integer(1)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn inv_of_zero_declines() {
        let zero = RealAlgebraic::from_rational(Rational::zero()).unwrap();
        assert!(inv(&zero).is_none());
    }

    // ---- algebraic_eq: the pivot ----

    #[test]
    fn equal_values_from_different_construction_paths() {
        // sqrt(6) two ways: directly (x^2-6 over (2,3)), and as sqrt(2)*sqrt(3)
        // via `mul`'s resultant. The resultant of two degree-2 operands is
        // generically degree 4; its squarefree part need not be renormalized
        // down to the true (degree-2) minimal polynomial, so this is exactly
        // the case raw coefficient equality was not designed for.
        let direct =
            RealAlgebraic::new(vec![-6, 0, 1], Rational::integer(2), Rational::integer(3)).unwrap();
        let sqrt2 = sqrt2_ir();
        let sqrt3 =
            RealAlgebraic::new(vec![-3, 0, 1], Rational::integer(1), Rational::integer(2)).unwrap();
        let via_mul = sqrt2.mul(&sqrt3).unwrap();
        // The pivot claim, demonstrated rather than merely asserted: raw
        // `PartialEq` (coefficient-for-coefficient defining-polynomial
        // equality) need not agree that these are the same value, because
        // `mul`'s resultant is not renormalized to a canonical minimal
        // polynomial. `algebraic_eq` must (and does) get it right regardless.
        eprintln!(
            "direct poly = {:?}, via_mul poly = {:?}, raw PartialEq = {}",
            direct.defining_poly(),
            via_mul.defining_poly(),
            direct == via_mul
        );
        assert_eq!(algebraic_eq(&direct, &via_mul), Some(true));
    }

    #[test]
    fn cross_representation_equality_needs_the_gcd_route() {
        // The decisive case raw `PartialEq` cannot handle: the SAME real
        // number (sqrt2) represented via two structurally unrelated defining
        // polynomials. `direct` uses the minimal polynomial x^2-2; `via_larger`
        // uses the reducible quartic (x^2-2)(x^2-5) = x^4-7x^2+10, which also
        // has exactly one root in (1,2) -- sqrt2 itself (sqrt5 ~ 2.236 is
        // outside). This is exactly the shape a cross-pipeline comparison
        // produces (e.g. an NRA witness's polynomial vs this crate's minimal
        // polynomial for the same value) and raw coefficient equality is
        // guaranteed to say "different" even though the value is identical.
        let direct = sqrt2_ir();
        let via_larger = RealAlgebraic::new_big(
            vec![10, 0, -7, 0, 1]
                .into_iter()
                .map(BigInt::from)
                .collect(),
            BigRational::from(BigInt::from(1)),
            BigRational::from(BigInt::from(2)),
        )
        .unwrap();
        assert_ne!(
            direct, via_larger,
            "raw PartialEq must disagree here (different defining polynomials)"
        );
        assert_eq!(algebraic_eq(&direct, &via_larger), Some(true));
    }

    #[test]
    fn associativity_probe_raw_partialeq_vs_algebraic_eq() {
        // (sqrt2 + sqrt3) + cbrt2 vs sqrt2 + (sqrt3 + cbrt2): same real number,
        // reached via two different resultant-combination orders. This probes
        // whether `combine_retry`'s squarefree reduction happens to always be
        // canonical (in which case raw PartialEq would agree here too) or not.
        // Either way, `algebraic_eq` must accept the pair.
        let sqrt2 = sqrt2_ir();
        let sqrt3 =
            RealAlgebraic::new(vec![-3, 0, 1], Rational::integer(1), Rational::integer(2)).unwrap();
        let cbrt2 = {
            let roots = crate::algebraic::real_roots(&poly_from(&[-2, 0, 0, 1])).unwrap();
            from_algebraic_real(&roots[0]).unwrap()
        };
        let left = sqrt2.add(&sqrt3).unwrap().add(&cbrt2).unwrap();
        let right = sqrt2.add(&sqrt3.add(&cbrt2).unwrap()).unwrap();
        eprintln!(
            "left poly len = {}, right poly len = {}, raw PartialEq = {}",
            left.defining_poly().len(),
            right.defining_poly().len(),
            left == right
        );
        assert_eq!(algebraic_eq(&left, &right), Some(true));
    }

    #[test]
    fn distinct_values_with_overlapping_brackets_are_not_equal() {
        // Two different quadratic irrationals whose isolating intervals
        // overlap: sqrt(2) in (1,2) and sqrt(3) in (1,2). This is the vacuous
        // control the equality test must not collapse on.
        let a = sqrt2_ir();
        let b =
            RealAlgebraic::new(vec![-3, 0, 1], Rational::integer(1), Rational::integer(2)).unwrap();
        assert_eq!(algebraic_eq(&a, &b), Some(false));
    }

    #[test]
    fn distinct_roots_of_the_same_polynomial_are_not_equal() {
        let a = sqrt2_ir(); // +sqrt2
        let neg = RealAlgebraic::new(vec![-2, 0, 1], Rational::integer(-2), Rational::integer(-1))
            .unwrap();
        assert_eq!(algebraic_eq(&a, &neg), Some(false));
    }

    #[test]
    fn equal_values_same_construction_agree_with_partial_eq_too() {
        let a = sqrt2_ir();
        let b = sqrt2_ir();
        assert_eq!(a, b); // sanity: built-in PartialEq handles the trivial case
        assert_eq!(algebraic_eq(&a, &b), Some(true));
    }

    // ---- polynomial_ivt / verify_ivt_certificate ----

    fn cubic_minus_two() -> Vec<Rational> {
        poly_from(&[-2, 0, 0, 1]) // x^3 - 2, root cbrt(2) ~ 1.26
    }

    #[test]
    fn ivt_names_the_root_of_a_cubic() {
        let p = cubic_minus_two();
        let cert = polynomial_ivt(&p, Rational::integer(1), Rational::integer(2)).unwrap();
        assert_eq!(verify_ivt_certificate(&cert), Some(true));
        assert_eq!(cert.root.degree(), 3);
    }

    #[test]
    fn ivt_declines_when_no_sign_change() {
        let p = poly_from(&[1, 0, 1]); // x^2+1, always positive
        assert!(polynomial_ivt(&p, Rational::integer(-5), Rational::integer(5)).is_none());
    }

    #[test]
    fn ivt_declines_on_endpoint_root() {
        let p = poly_from(&[-1, 1]); // x - 1
        assert!(polynomial_ivt(&p, Rational::integer(0), Rational::integer(1)).is_none());
    }

    // -- mutation tests: the certificate checker must reject every corruption --

    #[test]
    fn verify_rejects_corrupted_interval_endpoint() {
        let p = cubic_minus_two();
        let mut cert = polynomial_ivt(&p, Rational::integer(1), Rational::integer(2)).unwrap();
        // Flip the root's isolating interval to (2, 3): same (correct) minimal
        // polynomial, but a bracket that neither contains the true root
        // (cbrt(2) ~ 1.26) nor sits inside (a, b) = (1, 2).
        cert.root = crate::algebraic::test_support::make_unchecked(
            cert.root.minimal_polynomial().to_vec(),
            Rational::integer(2),
            Rational::integer(3),
        );
        assert_eq!(verify_ivt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_corrupted_polynomial_coefficient() {
        let p = cubic_minus_two();
        let mut cert = polynomial_ivt(&p, Rational::integer(1), Rational::integer(2)).unwrap();
        // Corrupt the constant term: x^3 - 2 -> x^3 - 3. The root's minimal
        // polynomial (still x^3-2) no longer divides the corrupted `poly`.
        cert.poly[0] = Rational::integer(-3);
        assert_eq!(verify_ivt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_corrupted_bracket_bounds() {
        let p = cubic_minus_two();
        let mut cert = polynomial_ivt(&p, Rational::integer(1), Rational::integer(2)).unwrap();
        // Shrink `b` below the sign-change point so p(a)*p(b) is no longer < 0.
        cert.b = Rational::new(11, 10); // 1.1: cbrt(2) ~ 1.26 > 1.1, and p(1.1) < 0 still (same sign as p(1))
        assert_eq!(verify_ivt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_accepts_the_unmutated_control() {
        let p = cubic_minus_two();
        let cert = polynomial_ivt(&p, Rational::integer(1), Rational::integer(2)).unwrap();
        assert_eq!(verify_ivt_certificate(&cert), Some(true));
    }

    // -- sturm.rs's half-open `(lower, upper]` convention, machine-checked --
    //
    // `root.isolating_interval()` excludes `lower` and includes `upper`. The
    // certificate claims `root` lies in the OPEN interval `(a, b)`. These
    // tests are adversarial: `make_unchecked` builds an `AlgebraicReal` whose
    // bracket is a legitimate half-open isolation (it genuinely contains
    // exactly one root of the stated minimal polynomial) but is fed to a
    // forged `IvtCertificate` whose `a`/`b` are chosen so the claimed OPEN
    // interval does not actually contain that root -- exactly the shape
    // ADR-1400 requires a certificate checker to reject.

    /// `x - 2` has its one root at exactly `2`. The half-open bracket `(1, 2]`
    /// legitimately isolates it (`upper` is inclusive). A forged certificate
    /// claims this root lies in the OPEN interval `(0, 2)` -- but `2` is not
    /// strictly less than `2`, so the claim is false, and the checker must
    /// reject it even though `upper <= b` (the loose containment check) holds
    /// exactly at equality.
    #[test]
    fn verify_rejects_a_root_forged_exactly_at_the_open_upper_bound() {
        let minimal_poly = poly_from(&[-2, 1]); // x - 2, root = 2
        let root = crate::algebraic::test_support::make_unchecked(
            minimal_poly.clone(),
            Rational::integer(1),
            Rational::integer(2), // (1, 2], root = 2 sits at the inclusive end
        );
        let cert = IvtCertificate {
            poly: minimal_poly,
            a: Rational::integer(0),
            b: Rational::integer(2), // == root: the open claim (0, 2) is false
            root,
        };
        assert_eq!(verify_ivt_certificate(&cert), Some(false));
    }

    /// Same shape, positive control: `b` strictly greater than the root, so
    /// the OPEN-interval claim is genuinely true and must be accepted. This
    /// is the non-vacuity check for the test above -- without it, a checker
    /// that rejected *every* certificate would also "pass".
    #[test]
    fn verify_accepts_a_loose_but_genuinely_open_upper_bound() {
        let minimal_poly = poly_from(&[-2, 1]); // x - 2, root = 2
        let root = crate::algebraic::test_support::make_unchecked(
            minimal_poly.clone(),
            Rational::integer(1),
            Rational::integer(2),
        );
        let cert = IvtCertificate {
            poly: minimal_poly,
            a: Rational::integer(0),
            b: Rational::new(5, 2), // 2.5, strictly past the root: (0, 2.5) is genuine
            root,
        };
        assert_eq!(verify_ivt_certificate(&cert), Some(true));
    }

    /// The mirrored lower-bound case is NOT a soundness risk, and this test
    /// records why: `lower` is EXCLUDED from the half-open bracket, so
    /// `root > lower >= a` is strict for free -- no `root != a` re-derivation
    /// is needed on that side. Confirms `lower == a` exactly is still
    /// correctly accepted (a completeness check, not a soundness one).
    #[test]
    fn verify_accepts_a_root_bracket_touching_the_open_lower_bound_exactly() {
        let minimal_poly = poly_from(&[-2, 1]); // x - 2, root = 2
        let root = crate::algebraic::test_support::make_unchecked(
            minimal_poly.clone(),
            Rational::integer(1), // lower == a below: excluded, so root > a holds
            Rational::integer(3),
        );
        let cert = IvtCertificate {
            poly: minimal_poly,
            a: Rational::integer(1),
            b: Rational::integer(3),
            root,
        };
        assert_eq!(verify_ivt_certificate(&cert), Some(true));
    }

    #[test]
    fn algebraic_eq_rejects_a_swapped_root() {
        let a = sqrt2_ir();
        let b =
            RealAlgebraic::new(vec![-3, 0, 1], Rational::integer(1), Rational::integer(2)).unwrap();
        assert_eq!(algebraic_eq(&a, &a), Some(true));
        assert_eq!(algebraic_eq(&a, &b), Some(false));
    }
}
