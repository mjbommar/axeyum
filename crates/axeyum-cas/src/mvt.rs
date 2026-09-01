//! Exact polynomial MEAN VALUE THEOREM (ADR-0603 row 3): the classical MVT on
//! the decidable fragment.
//!
//! ## Where this sits in the graded family (ADR-0603, `docs/curriculum/graded-statement-families.md` §1)
//!
//! MVT is classically unavailable here in general: it rests on the Extreme
//! Value Theorem, which is constructively out of reach for an arbitrary
//! uniformly continuous `F` (see
//! `crates/axeyum-lean-kernel/src/creal/monotone.rs`'s module doc, and this
//! crate's own [`crate::extremum`] row 2 note). But on the **decidable
//! fragment** -- polynomials with rational coefficients on a rational closed
//! interval -- zero-testing is decidable, so the full classical statement is
//! reachable exactly, axiom-free, executable, mirroring how [`crate::extremum`]
//! reaches EVT on the same fragment:
//!
//! 1. **Row 1/2** (kernel side): the constructive substitutes
//!    (`CReal.monotone_of_nonneg_deriv`, …) and the (in-progress) EVT
//!    refutation MVT classically depends on.
//! 3. **Row 3 (this file)**: for a polynomial `p` with rational coefficients
//!    on `[a, b]` with rational `a < b`, there exists `c ∈ (a, b)` with
//!    `p'(c) = (p(b) − p(a))/(b − a)`, and `c` is produced as a **named**
//!    [`AlgebraicReal`] with a certificate -- not merely asserted to exist.
//! 4. Row 4 (labeled import, not attempted here): the classical MVT for
//!    arbitrary continuous `F`, imported with visible axiom footprint.
//!
//! ## Why a sibling module rather than extending `extremum.rs`
//!
//! Same reasoning [`crate::extremum`]'s own module doc gives for splitting out
//! of `real_algebraic.rs`: this file's logic (form the Rolle reduction `g`,
//! find an interior root of `g'`, name it) is a distinct concern with its own
//! certificate shape and its own degenerate cases, and it *reuses*
//! [`crate::extremum::polynomial_extremum`] as a black box rather than
//! duplicating its critical-point search.
//!
//! ## The construction (the classical proof, made exact)
//!
//! Given `p`, `a < b` (rational), let `m := (p(b) − p(a))/(b − a)` (the exact
//! secant slope, rational since `p(a)`, `p(b)`, `a`, `b` all are) and form
//!
//! ```text
//! g(x) := p(x) − p(a) − m·(x − a)
//! ```
//!
//! Then `g(a) = 0` and `g(b) = p(b) − p(a) − m(b−a) = p(b) − p(a) − (p(b) − p(a)) = 0`
//! *by construction* (checked, not assumed, by [`verify_mvt_certificate`]).
//! MVT's conclusion `p'(c) = m` is exactly `g'(c) = 0` for some `c ∈ (a, b)` --
//! this is **Rolle's theorem** applied to `g`, and establishing it honestly is
//! the mathematical content of this file (see the next section). `g'(x) =
//! p'(x) − m` is a rational polynomial; the certificate carries both `g` and
//! `g'` explicitly, each checked against a fresh recomputation from `poly`,
//! `a`, `b` alone.
//!
//! ## The existence argument (why an interior root of `g'` is guaranteed)
//!
//! This is the step a search-only implementation would hand-wave, so it is
//! spelled out: `g(a) = g(b) = 0`, so both endpoints are always among the
//! candidates [`crate::extremum::polynomial_extremum`] considers for `g`'s
//! maximum on `[a, b]`, which makes `max(g) ≥ 0` unconditionally. Two cases:
//!
//! - **`deg(p) ≤ 1`** (`p` constant or linear): `g` is identically the zero
//!   polynomial (a constant function has zero secant slope and zero
//!   derivative everywhere; a linear function's derivative *is* its secant
//!   slope everywhere), so `g' ≡ 0` and **every** point of `(a, b)` is a Rolle
//!   witness. Handled as its own branch below, without invoking
//!   [`crate::extremum::polynomial_extremum`] at all -- see "Degenerate
//!   cases".
//! - **`deg(p) ≥ 2`**: then `deg(g) = deg(p) ≥ 2` (subtracting a linear term
//!   cannot change a degree-≥2 leading term), so `g` has at most `deg(g)`
//!   real roots — a *finite* set. If `g` were identically zero on `[a, b]`,
//!   it would have infinitely many roots there, forcing it to be the zero
//!   polynomial everywhere (a nonzero polynomial has finitely many roots),
//!   which would make `p(x) = p(a) + m(x − a)` affine — contradicting
//!   `deg(p) ≥ 2`. So `g` is **not** identically zero on `[a, b]`, hence takes
//!   some nonzero value there, hence either `max(g) > 0` or `min(g) < 0`
//!   (both cannot be `0` while `g` is nonzero somewhere on a continuum).
//!   Whichever holds, that extremum's value is **strictly greater** than both
//!   endpoint values (both `0`), so [`crate::extremum::polynomial_extremum`]'s
//!   own completeness argument forces the argmax/argmin to be an **interior
//!   critical point** — a root of `g'` strictly inside `(a, b)`, by Fermat's
//!   interior-extremum theorem, which is exactly [`crate::extremum`]'s own
//!   completeness argument reused rather than re-derived. This module calls
//!   [`crate::extremum::polynomial_extremum`] on `g`, and if its argmax is not
//!   `Critical` (i.e. `max(g) = 0`, both endpoints tie the max), calls it
//!   again on `−g` to find the min case; one of the two is guaranteed to
//!   locate an interior critical point by the argument above, so a `None`
//!   from both is a decline in the underlying extremum search (a degree/cap
//!   issue), never a genuine mathematical absence.
//!
//! The certificate itself does **not** need to re-derive this existence
//! argument to be checkable: [`verify_mvt_certificate`] only needs to confirm,
//! *locally*, that the stored `c` really is a strictly-interior root of the
//! recomputed `g'` — the same "certificate is data, not a trace of the
//! search" split [`crate::extremum`] and
//! [`crate::real_algebraic::polynomial_ivt`] already use.
//!
//! ## Degenerate cases (must not panic)
//!
//! - **`a == b`**: no secant slope is defined (division by `b − a = 0`);
//!   [`polynomial_mvt`] declines (`None`) before computing it.
//! - **`p` constant**: `g' ≡ 0` (see above); every point of `(a, b)` is a
//!   witness. The midpoint `(a+b)/2` is named as `c`, represented as a genuine
//!   [`AlgebraicReal`] (via [`crate::algebraic::real_roots`] on its own
//!   degree-1 defining polynomial, reusing the existing isolation route rather
//!   than hand-building one).
//! - **`p` linear**: same as constant — `g' ≡ 0` because a linear function's
//!   derivative already equals its secant slope everywhere. Same midpoint
//!   handling.
//! - **`p` of high degree where the underlying extremum search declines**
//!   (Sturm isolation's degree cap, or the resultant dimension cap
//!   `BIG_MAX_SYLVESTER_DIM` inside evaluation): [`polynomial_mvt`] returns
//!   `None` for the *whole* certificate. There is nothing to "drop" here —
//!   unlike [`crate::extremum`], which iterates a finite *candidate list* and
//!   must not silently omit one, MVT only ever needs to name *one* witness, so
//!   a decline in locating it aborts the whole call rather than reporting a
//!   partial answer.
//!
//! ## Scope
//!
//! Univariate, rational coefficients, closed interval `[a, b]` with rational
//! endpoints, `a < b` strictly. Same scope as [`crate::extremum`], for the
//! same reasons (open intervals, algebraic endpoints, and multivariate `p`
//! would each need a different argument).
//!
//! ## Cost
//!
//! [`polynomial_mvt`] costs at most two calls to
//! [`crate::extremum::polynomial_extremum`] (on `g` and, only if the first
//! does not locate an interior critical point, on `−g`) plus O(deg `p`) exact
//! arithmetic to build `g`/`g'`. **This is NOT simply [`crate::extremum`]'s
//! cost curve inherited unchanged**, and an earlier draft of this doc claimed
//! it was before measuring: subtracting a nonzero secant slope `m` from `p'`
//! generally destroys whatever rational/low-degree factorization made the
//! *original* `p'` cheap to isolate, because `p' − m` is a differently-shaped
//! polynomial with no reason to share `p'`'s roots or factor structure.
//! `cost_curve_where_it_hurts_thick_degree_5_declines_soundly` (below) is the
//! measured counterexample: it reuses the exact polynomial
//! `crate::extremum::tests::cost_curve_by_degree` reports as its *cheap,
//! all-rational* degree-5 case (because there `p' = 0` is solved directly,
//! with `m` implicitly `0`), and on `[−2, 2]` (secant slope `28 ≠ 0`) it
//! instead declines in a few seconds hitting the resultant dimension cap, because
//! `p' − 28` is an irreducible quartic with none of `p'`'s structure.
//! `cost_curve_by_degree` measures three *chosen-to-be-cheap* cases directly
//! through this module's own entry point (deg 2: ~3 ms; deg 3, irrational
//! witness: ~8 ms; deg 5 with a degree-4 algebraic witness, chosen so the
//! evaluation reduces to a single linear term: ~43 ms; debug build, one
//! measurement, not a ratchet). `verify_mvt_certificate` itself is cheap by
//! comparison regardless (one Sturm recount + a handful of exact polynomial
//! evaluations, no search).

use core::cmp::Ordering;

use axeyum_ir::{Rational, RealAlgebraic, poly};

use crate::algebraic::AlgebraicReal;
use crate::extremum::ExtremumLocation;
use crate::real_algebraic::{algebraic_cmp, eval_poly_at_algebraic};
use crate::sturm;

/// A checkable certificate for the exact polynomial Mean Value Theorem: `poly`
/// has secant slope `slope` on `[a, b]`, and `c` **is** a point strictly
/// inside `(a, b)` with `poly'(c) = slope`, named exactly (as an
/// [`AlgebraicReal`]), not approximated.
///
/// This is *data*, not a trace of the search that found it:
/// [`verify_mvt_certificate`] re-derives every check from `poly`, `a`, `b`,
/// `slope`, `g`, `deriv_g`, and `c` alone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MvtCertificate {
    /// The polynomial `p` (LSB-first, rational coefficients, trimmed).
    pub poly: Vec<Rational>,
    /// The left interval endpoint.
    pub a: Rational,
    /// The right interval endpoint, with `a < b`.
    pub b: Rational,
    /// The exact secant slope `m = (p(b) − p(a)) / (b − a)`.
    pub slope: Rational,
    /// The Rolle reduction `g(x) = p(x) − p(a) − slope·(x − a)`, carried
    /// explicitly so the checker can compare it against an independent
    /// recomputation from `poly`, `a`, `slope` (catches a corrupted `poly` or
    /// a corrupted `g` — either way the two must still agree).
    pub g: Vec<Rational>,
    /// `g' = poly' − slope`, likewise carried explicitly for the same reason.
    pub deriv_g: Vec<Rational>,
    /// The named MVT witness, strictly inside `(a, b)`.
    pub c: AlgebraicReal,
}

/// The Rolle reduction `g(x) = p(x) − p(a) − slope·(x − a)`, given `p(a)`
/// already evaluated. `None` on overflow.
fn build_g(
    trimmed: &[Rational],
    a: Rational,
    pa: Rational,
    slope: Rational,
) -> Option<Vec<Rational>> {
    let c0 = pa.checked_sub(slope.checked_mul(a)?)?;
    let mut g = trimmed.to_vec();
    while g.len() < 2 {
        g.push(Rational::zero());
    }
    g[0] = g[0].checked_sub(c0)?;
    g[1] = g[1].checked_sub(slope)?;
    Some(poly::rat_trim(g))
}

/// `g' = p' − slope`. `None` on overflow.
fn build_deriv_g(trimmed: &[Rational], slope: Rational) -> Option<Vec<Rational>> {
    let mut deriv = poly::rat_derivative(trimmed)?;
    if deriv.is_empty() {
        deriv.push(Rational::zero());
    }
    deriv[0] = deriv[0].checked_sub(slope)?;
    Some(poly::rat_trim(deriv))
}

/// Represent a rational value `c` as a genuine [`AlgebraicReal`], by isolating
/// the (unique) root of its own degree-1 defining polynomial via
/// [`crate::algebraic::real_roots`] — reusing the existing isolation route
/// rather than hand-building an unchecked bracket.
fn rational_as_algebraic_real(c: Rational) -> Option<AlgebraicReal> {
    let linear = vec![
        Rational::integer(c.numerator()).checked_neg()?,
        Rational::integer(c.denominator()),
    ];
    let mut roots = crate::algebraic::real_roots(&linear)?;
    roots.pop()
}

/// The outcome of one attempt (on `g` or `−g`) to locate an interior
/// critical point via [`crate::extremum::polynomial_extremum`].
enum WitnessSearch {
    /// The underlying extremum search declined (a sound decline;
    /// [`polynomial_mvt`] propagates it rather than trying to guess).
    Decline,
    /// The search succeeded but the extremum sat at an endpoint (a tie with
    /// `g(a) = g(b) = 0`) rather than interior; try the other sign.
    NotInterior,
    /// A genuine interior critical point, strictly inside `(a, b)`.
    Found(AlgebraicReal),
}

/// Try to locate an interior critical point of `g` (or, if `negate`, of `−g`)
/// via [`crate::extremum::polynomial_extremum`], reporting it only if the
/// located extremum is **strictly greater than zero** — which (given
/// `g(a) = g(b) = 0`) is exactly the condition that forces the argmax to be
/// interior rather than an endpoint tie.
fn interior_extremum_witness(
    g: &[Rational],
    a: Rational,
    b: Rational,
    negate: bool,
) -> WitnessSearch {
    let target: Option<Vec<Rational>> = if negate {
        g.iter().map(|coeff| coeff.checked_neg()).collect()
    } else {
        Some(g.to_vec())
    };
    let Some(target) = target else {
        return WitnessSearch::Decline;
    };
    let Some(cert) = crate::extremum::polynomial_extremum(&target, a, b) else {
        return WitnessSearch::Decline;
    };
    let ExtremumLocation::Critical(idx) = cert.argmax else {
        return WitnessSearch::NotInterior;
    };
    let Some(zero) = RealAlgebraic::from_rational(Rational::zero()) else {
        return WitnessSearch::Decline;
    };
    match algebraic_cmp(&cert.max_value, &zero) {
        Some(Ordering::Greater) => WitnessSearch::Found(cert.critical_points[idx].clone()),
        Some(_) => WitnessSearch::NotInterior,
        None => WitnessSearch::Decline,
    }
}

/// Produce an [`MvtCertificate`] for `poly` on `[a, b]`.
///
/// `None` if `a >= b` (no secant slope is defined for a degenerate or
/// backwards interval), or on any underlying differentiation/isolation/
/// arithmetic decline — see the module doc's "Degenerate cases". A decline
/// here is sound: it never returns a certificate whose witness is wrong or
/// non-interior.
#[must_use]
pub fn polynomial_mvt(
    poly_coeffs: &[Rational],
    a: Rational,
    b: Rational,
) -> Option<MvtCertificate> {
    if a.checked_cmp(&b)? != Ordering::Less {
        return None;
    }
    let trimmed = poly::rat_trim(poly_coeffs.to_vec());
    let pa = poly::eval_rat_poly(&trimmed, a)?;
    let pb = poly::eval_rat_poly(&trimmed, b)?;
    let width = b.checked_sub(a)?;
    let slope = pb.checked_sub(pa)?.checked_div(width)?;

    let g = build_g(&trimmed, a, pa, slope)?;
    let deriv_g = build_deriv_g(&trimmed, slope)?;

    if poly::rat_trim(deriv_g.clone()).is_empty() {
        // g' ≡ 0 identically: p has degree <= 1. Every point of (a, b) works;
        // name the midpoint (see module doc's "Degenerate cases").
        let c_rat = a.checked_add(b)?.checked_div(Rational::integer(2))?;
        let c = rational_as_algebraic_real(c_rat)?;
        return Some(MvtCertificate {
            poly: trimmed,
            a,
            b,
            slope,
            g,
            deriv_g,
            c,
        });
    }

    // General case (deg p >= 2): Rolle via an interior extremum of g -- see
    // the module doc's existence argument.
    if let WitnessSearch::Found(c) = interior_extremum_witness(&g, a, b, false) {
        return Some(MvtCertificate {
            poly: trimmed,
            a,
            b,
            slope,
            g,
            deriv_g,
            c,
        });
    }
    if let WitnessSearch::Found(c) = interior_extremum_witness(&g, a, b, true) {
        return Some(MvtCertificate {
            poly: trimmed,
            a,
            b,
            slope,
            g,
            deriv_g,
            c,
        });
    }
    // Mathematically unreachable per the module doc's existence argument (one
    // of the two calls above must locate an interior critical point when
    // deg(p) >= 2) -- if both returned NotInterior, the underlying extremum
    // search itself must have found max(g) = min(g) = 0 with g not
    // identically zero, a contradiction; treat it as a sound decline rather
    // than trust that reasoning at the call site.
    None
}

/// Independently re-derive and check an [`MvtCertificate`]:
///
/// 1. Confirm `a < b`.
/// 2. Recompute the secant slope from `poly`, `a`, `b` and confirm it matches
///    the stored `slope`.
/// 3. Recompute `g` and `g'` from `poly`/`a`/`slope` and confirm they match
///    the stored `g`/`deriv_g` (the Rolle-reduction identity witnesses).
/// 4. Confirm `c`'s own bracket genuinely isolates exactly one root of its
///    stated minimal polynomial (never trust the stored bracket's own
///    bookkeeping) — mirrors [`crate::extremum::verify_extremum_certificate`]
///    and [`crate::real_algebraic::verify_ivt_certificate`].
/// 5. Confirm `c` is **strictly** interior to `(a, b)` — an endpoint root is
///    not MVT, however good the arithmetic on it looks (see this module's
///    `verify_rejects_an_endpoint_witness` test for a case where the slope
///    equation alone would falsely pass at an endpoint).
/// 6. Confirm `c` is a genuine root of the recomputed `g'`, evaluated exactly.
/// 7. Confirm the stated conclusion itself: `p'(c) = slope`, re-derived from
///    `poly` alone.
///
/// `Some(true)` — valid; `Some(false)` — the certificate is definitely wrong;
/// `None` — declined (overflow/degree cap), never a false accept.
#[must_use]
pub fn verify_mvt_certificate(cert: &MvtCertificate) -> Option<bool> {
    let MvtCertificate {
        poly,
        a,
        b,
        slope,
        g,
        deriv_g,
        c,
    } = cert;

    // Step 1.
    let Some(Ordering::Less) = a.checked_cmp(b) else {
        return Some(false);
    };

    // Step 2.
    let pa = poly::eval_rat_poly(poly, *a)?;
    let pb = poly::eval_rat_poly(poly, *b)?;
    let width = b.checked_sub(*a)?;
    let recomputed_slope = pb.checked_sub(pa)?.checked_div(width)?;
    if recomputed_slope != *slope {
        return Some(false);
    }

    // Step 3.
    let recomputed_g = build_g(poly, *a, pa, *slope)?;
    if recomputed_g != poly::rat_trim(g.clone()) {
        return Some(false);
    }
    let recomputed_deriv_g = build_deriv_g(poly, *slope)?;
    if recomputed_deriv_g != poly::rat_trim(deriv_g.clone()) {
        return Some(false);
    }

    // Step 4.
    let (lower, upper) = c.isolating_interval();
    if lower.checked_cmp(&upper)? != Ordering::Less {
        return Some(false);
    }
    match sturm::count_real_roots_in(c.minimal_polynomial(), lower, upper) {
        Some(1) => {}
        Some(_) => return Some(false),
        None => return None,
    }

    // Step 5.
    let lifted_c = crate::real_algebraic::from_algebraic_real(c)?;
    let above_a = lifted_c.compare_rational(a)?;
    let below_b = lifted_c.compare_rational(b)?;
    if above_a != Ordering::Greater || below_b != Ordering::Less {
        return Some(false);
    }

    // Step 6.
    let zero = RealAlgebraic::from_rational(Rational::zero())?;
    let g_prime_at_c = eval_poly_at_algebraic(&recomputed_deriv_g, c)?;
    if algebraic_cmp(&g_prime_at_c, &zero)? != Ordering::Equal {
        return Some(false);
    }

    // Step 7.
    let p_prime = poly::rat_derivative(poly)?;
    let p_prime_at_c = eval_poly_at_algebraic(&p_prime, c)?;
    let slope_as_algebraic = RealAlgebraic::from_rational(*slope)?;
    if algebraic_cmp(&p_prime_at_c, &slope_as_algebraic)? != Ordering::Equal {
        return Some(false);
    }

    Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Rational;
    use std::time::Instant;

    fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().map(|&c| Rational::integer(c)).collect()
    }

    // ---- correctness spot-checks with known answers ----

    #[test]
    fn quadratic_rational_witness() {
        // p = x^2 on [0, 2]: slope = (4-0)/2 = 2, and MVT's witness is
        // c = 1 exactly (p'(1) = 2).
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_mvt(&p, Rational::integer(0), Rational::integer(2))
            .expect("must not decline");
        assert_eq!(verify_mvt_certificate(&cert), Some(true));
        assert_eq!(cert.slope, Rational::integer(2));
        assert_eq!(cert.c.rational_value(), Some(Rational::integer(1)));
    }

    #[test]
    fn cubic_irrational_witness_x_cubed_on_0_3() {
        // p = x^3 on [0, 3]: slope = (27-0)/3 = 9, p' = 3x^2, so p'(c) = 9
        // means c^2 = 3, c = sqrt(3) -- irrational, exact arithmetic gets it
        // right where floating point would fumble.
        let p = poly_from(&[0, 0, 0, 1]);
        let cert = polynomial_mvt(&p, Rational::integer(0), Rational::integer(3))
            .expect("must not decline");
        assert_eq!(verify_mvt_certificate(&cert), Some(true));
        assert_eq!(cert.slope, Rational::integer(9));
        // c must be genuinely irrational (no rational value) and of algebraic
        // degree 2, the minimal polynomial of sqrt(3) (x^2 - 3, up to scale).
        assert_eq!(
            cert.c.rational_value(),
            None,
            "c = sqrt(3) must be irrational"
        );
        assert_eq!(cert.c.degree(), 2);
        // Bracket sqrt(3) ~= 1.732 exactly, no floating point: 1 < c < 2.
        let lifted = crate::real_algebraic::from_algebraic_real(&cert.c).unwrap();
        assert_eq!(
            lifted.compare_rational(&Rational::integer(1)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            lifted.compare_rational(&Rational::integer(2)),
            Some(Ordering::Less)
        );
    }

    #[test]
    fn linear_degenerate_case_x_on_0_1() {
        // p = x on [0, 1]: slope = 1 = p' everywhere; g' == 0 identically,
        // the degenerate branch. Any interior point works; the midpoint is
        // named.
        let p = poly_from(&[0, 1]);
        let cert = polynomial_mvt(&p, Rational::integer(0), Rational::integer(1))
            .expect("must not decline");
        assert_eq!(verify_mvt_certificate(&cert), Some(true));
        assert!(
            poly::rat_trim(cert.deriv_g.clone()).is_empty(),
            "g' must be identically zero"
        );
        assert_eq!(cert.slope, Rational::integer(1));
        assert_eq!(
            cert.c.rational_value(),
            Some(Rational::checked_new(1, 2).unwrap()),
            "midpoint of [0,1]"
        );
    }

    // ---- degenerate cases ----

    #[test]
    fn constant_polynomial_degenerate_case() {
        let p = poly_from(&[7]);
        let cert = polynomial_mvt(&p, Rational::integer(-1), Rational::integer(1))
            .expect("must not decline");
        assert_eq!(verify_mvt_certificate(&cert), Some(true));
        assert_eq!(cert.slope, Rational::zero());
        assert!(poly::rat_trim(cert.deriv_g.clone()).is_empty());
        assert_eq!(
            cert.c.rational_value(),
            Some(Rational::zero()),
            "midpoint of [-1,1]"
        );
    }

    #[test]
    fn degenerate_interval_a_equals_b_declines() {
        let p = poly_from(&[0, 0, 1]);
        assert_eq!(
            polynomial_mvt(&p, Rational::integer(5), Rational::integer(5)),
            None,
            "a == b must decline, not divide by zero"
        );
    }

    #[test]
    fn backwards_interval_a_greater_than_b_declines() {
        let p = poly_from(&[0, 0, 1]);
        assert_eq!(
            polynomial_mvt(&p, Rational::integer(2), Rational::integer(0)),
            None
        );
    }

    #[test]
    fn zero_polynomial_is_degenerate() {
        let p = poly_from(&[0]);
        let cert = polynomial_mvt(&p, Rational::integer(-2), Rational::integer(4))
            .expect("must not decline");
        assert_eq!(verify_mvt_certificate(&cert), Some(true));
        assert_eq!(cert.slope, Rational::zero());
    }

    #[test]
    fn high_degree_declines_soundly_never_panics() {
        // p' = x^4 - 2 (irreducible degree-4 real roots) composed against a
        // degree-5 p, mirroring extremum.rs's own cap-adjacent probe: whether
        // it accepts or soundly declines, it must not panic, and an accept
        // must independently verify.
        let p = poly_from(&[0, -10, 0, 0, 0, 5]);
        let t0 = Instant::now();
        let result = polynomial_mvt(&p, Rational::integer(-3), Rational::integer(3));
        let elapsed = t0.elapsed();
        eprintln!(
            "high-degree probe: elapsed={elapsed:?} declined={}",
            result.is_none()
        );
        if let Some(cert) = result {
            assert_eq!(verify_mvt_certificate(&cert), Some(true));
        }
    }

    // ---- mutation tests: the checker must reject every corruption ----

    fn tie_case_cert() -> MvtCertificate {
        // p = x^3 - 3x on [-2, 2] (same shape as extremum.rs's tie test):
        // p(a)=p(b)=-2, slope=0... actually recompute: p(-2)=-8+6=-2,
        // p(2)=8-6=2, slope=(2-(-2))/4=1. p'=3x^2-3=1 => x^2=4/3, irrational,
        // two interior roots +-2/sqrt(3).
        let p = poly_from(&[0, -3, 0, 1]);
        polynomial_mvt(&p, Rational::integer(-2), Rational::integer(2)).expect("must not decline")
    }

    #[test]
    fn verify_accepts_the_unmutated_control() {
        assert_eq!(verify_mvt_certificate(&tie_case_cert()), Some(true));
    }

    #[test]
    fn verify_rejects_corrupted_polynomial_coefficient() {
        let mut cert = tie_case_cert();
        // Corrupt the LINEAR coefficient, not the constant one: adding a
        // constant to `poly` leaves `p'`, the secant slope, and `g` all
        // unchanged (shifting a function vertically changes neither its
        // derivative nor its secant slope), so that mutation is invisible to
        // this certificate by construction, not a gap in the checker.
        cert.poly[1] = cert.poly[1].checked_add(Rational::integer(5)).unwrap();
        assert_eq!(verify_mvt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_corrupted_slope() {
        let mut cert = tie_case_cert();
        cert.slope = cert.slope.checked_add(Rational::integer(1)).unwrap();
        assert_eq!(verify_mvt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_corrupted_g() {
        let mut cert = tie_case_cert();
        cert.g[0] = cert.g[0].checked_add(Rational::integer(1)).unwrap();
        assert_eq!(verify_mvt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_corrupted_deriv_g() {
        let mut cert = tie_case_cert();
        cert.deriv_g[0] = cert.deriv_g[0].checked_add(Rational::integer(1)).unwrap();
        assert_eq!(verify_mvt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_swapped_witness() {
        let mut cert = tie_case_cert();
        // sqrt(2), bracketed in (1, 2): not a root of this g' = 3x^2 - 4.
        cert.c = crate::algebraic::test_support::make_unchecked(
            poly_from(&[-2, 0, 1]),
            Rational::integer(1),
            Rational::integer(2),
        );
        assert_eq!(verify_mvt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_corrupted_bracket() {
        let mut cert = tie_case_cert();
        let original = cert.c.minimal_polynomial().to_vec();
        cert.c = crate::algebraic::test_support::make_unchecked(
            original,
            Rational::integer(-2),
            Rational::integer(-2),
        );
        assert_eq!(verify_mvt_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_an_endpoint_witness() {
        // The interesting case: p = x^3 - 4x^2 on [0, 4]. p(0) = 0, p(4) =
        // 64 - 64 = 0, so slope = 0. p' = 3x^2 - 8x = x(3x-8), roots at x = 0
        // (the LEFT ENDPOINT itself) and x = 8/3 (genuinely interior). Both
        // satisfy p'(x) = slope = 0 exactly -- so a checker that only tested
        // the slope equation would WRONGLY accept c = 0 as an MVT witness.
        // Only the strict-interiority check (step 5) catches this.
        let p = poly_from(&[0, 0, -4, 1]);
        let cert = polynomial_mvt(&p, Rational::integer(0), Rational::integer(4))
            .expect("must not decline");
        assert_eq!(cert.slope, Rational::zero());
        // Sanity: the genuine witness the producer found must be interior.
        assert_eq!(verify_mvt_certificate(&cert), Some(true));
        assert_ne!(cert.c.rational_value(), Some(Rational::zero()));

        // Now corrupt c to the endpoint x = 0 (a itself), which DOES satisfy
        // p'(0) = 0 = slope exactly.
        let mut mutated = cert;
        mutated.c = rational_as_algebraic_real(Rational::zero()).unwrap();
        // Confirm the coincidence: p'(0) really does equal slope, so the
        // slope-equation check ALONE would pass here.
        let p_prime = poly::rat_derivative(&mutated.poly).unwrap();
        let value_at_0 = eval_poly_at_algebraic(&p_prime, &mutated.c).unwrap();
        assert_eq!(
            algebraic_cmp(
                &value_at_0,
                &RealAlgebraic::from_rational(mutated.slope).unwrap()
            ),
            Some(Ordering::Equal),
            "sanity: p'(0) = slope really does hold, making this the adversarial case"
        );
        assert_eq!(
            verify_mvt_certificate(&mutated),
            Some(false),
            "an endpoint root is not MVT, however good the arithmetic looks"
        );
    }

    #[test]
    fn verify_rejects_an_endpoint_witness_at_the_right_bound() {
        // Mirror of `verify_rejects_an_endpoint_witness`, but at `b` instead
        // of `a` -- ADR-1435 found the sturm/real_algebraic IVT bridge's
        // strictness at the RIGHT endpoint rested on an incidental guard
        // that no test isolated; step 5 here (`below_b != Ordering::Less`)
        // is a single combined check covering both bounds, so this confirms
        // the right-endpoint branch is independently exercised too, not just
        // assumed symmetric with the left-endpoint test above.
        //
        // q(x) = -x^3 + 8x^2 - 16x on [0, 4]: q(0) = 0, q(4) = -64+128-64 = 0,
        // so slope = 0. q' = -3x^2 + 16x - 16, roots at x = 4/3 (genuinely
        // interior) and x = 4 (the RIGHT ENDPOINT itself, by construction --
        // q is p(4-x) for the left-endpoint example's p = x^3 - 4x^2,
        // reflecting its endpoint coincidence from a to b). Both satisfy
        // q'(x) = slope = 0 exactly.
        let q = poly_from(&[0, -16, 8, -1]);
        let cert = polynomial_mvt(&q, Rational::integer(0), Rational::integer(4))
            .expect("must not decline");
        assert_eq!(cert.slope, Rational::zero());
        // Sanity: the genuine witness the producer found must be interior
        // (4/3), not the endpoint (4).
        assert_eq!(verify_mvt_certificate(&cert), Some(true));
        assert_ne!(cert.c.rational_value(), Some(Rational::integer(4)));

        // Now corrupt c to the endpoint x = 4 (b itself), which DOES satisfy
        // q'(4) = 0 = slope exactly.
        let mut mutated = cert;
        mutated.c = rational_as_algebraic_real(Rational::integer(4)).unwrap();
        // Confirm the coincidence: q'(4) really does equal slope, so the
        // slope-equation check ALONE would pass here.
        let q_prime = poly::rat_derivative(&mutated.poly).unwrap();
        let value_at_4 = eval_poly_at_algebraic(&q_prime, &mutated.c).unwrap();
        assert_eq!(
            algebraic_cmp(
                &value_at_4,
                &RealAlgebraic::from_rational(mutated.slope).unwrap()
            ),
            Some(Ordering::Equal),
            "sanity: q'(4) = slope really does hold, making this the adversarial case"
        );
        assert_eq!(
            verify_mvt_certificate(&mutated),
            Some(false),
            "an endpoint root at b is not MVT either, however good the arithmetic looks"
        );
    }

    // ---- cost curve (wall clock; measured, not estimated) ----

    #[test]
    fn cost_curve_by_degree() {
        // Degree 2: p = x^2 on [0, 2] (rational witness, see
        // `quadratic_rational_witness`).
        let d2 = poly_from(&[0, 0, 1]);
        let t0 = Instant::now();
        let c2 = polynomial_mvt(&d2, Rational::integer(0), Rational::integer(2)).unwrap();
        let e2 = t0.elapsed();
        assert_eq!(verify_mvt_certificate(&c2), Some(true));

        // Degree 3: p = x^3 on [0, 3] (irrational witness c = sqrt(3)).
        let d3 = poly_from(&[0, 0, 0, 1]);
        let t1 = Instant::now();
        let c3 = polynomial_mvt(&d3, Rational::integer(0), Rational::integer(3)).unwrap();
        let e3 = t1.elapsed();
        assert_eq!(verify_mvt_certificate(&c3), Some(true));

        // Degree 5: p = x^5 on [0, 1]. slope = 1, p' = 5x^4, so the witness
        // solves 5x^4 = 1 -- a degree-4 irrational algebraic number. Chosen
        // (like `crate::extremum`'s own degree-5 case) so `g = x^5 - x`
        // reduces to a single linear term modulo the degree-4 minimal
        // polynomial (`rat_rem` gives `-4/5 * x`), keeping evaluation cheap
        // even though the critical point's own algebraic degree is 4.
        let d5 = poly_from(&[0, 0, 0, 0, 0, 1]);
        let t2 = Instant::now();
        let c5 = polynomial_mvt(&d5, Rational::integer(0), Rational::integer(1)).unwrap();
        let e5 = t2.elapsed();
        assert_eq!(verify_mvt_certificate(&c5), Some(true));
        assert_eq!(c5.c.degree(), 4);

        eprintln!("mvt cost curve: deg2={e2:?}, deg3={e3:?}, deg5(critical-degree4)={e5:?}");
    }

    #[test]
    fn cost_curve_where_it_hurts_thick_degree_5_declines_soundly() {
        // p = 3x^5 - 5x^3 on [-2, 2] -- the SAME polynomial
        // `crate::extremum::tests::cost_curve_by_degree` uses for its own
        // (cheap, all-rational) degree-5 case, because there p' = 0 is being
        // solved directly. Here the secant slope is 28 (nonzero), so MVT
        // instead needs a root of p' - 28 = 15x^4 - 15x^2 - 28, an
        // IRREDUCIBLE quartic with none of p''s rational structure -- and
        // evaluating `g` at that quartic root grows the accumulated
        // resultant degree fast enough to trip
        // `axeyum_ir::poly_big::BIG_MAX_SYLVESTER_DIM` (each single
        // evaluation declines in under 100 ms; `polynomial_mvt` tries both
        // `g` and `-g`, each evaluating both critical points before giving
        // up, so the whole call measures a few seconds -- 2-4 s measured
        // across runs, debug build). This is the module doc's warning
        // made concrete: subtracting a nonzero secant slope can turn an
        // `extremum`-cheap polynomial into an `mvt`-expensive one, because
        // the shifted derivative rarely inherits the original's factorable
        // structure. A sound decline (`None`), never a wrong witness or a
        // panic, either way.
        let p = poly_from(&[0, 0, 0, -5, 0, 3]);
        let t0 = Instant::now();
        let result = polynomial_mvt(&p, Rational::integer(-2), Rational::integer(2));
        let elapsed = t0.elapsed();
        eprintln!(
            "mvt cost curve (hurts): elapsed={elapsed:?} declined={}",
            result.is_none()
        );
        if let Some(cert) = result {
            assert_eq!(verify_mvt_certificate(&cert), Some(true));
        }
    }
}
