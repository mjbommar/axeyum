//! Exact polynomial EXTREMUM (ADR-0603 row 3): the Extreme Value Theorem on
//! the decidable fragment.
//!
//! ## Where this sits in the graded family (ADR-0603)
//!
//! EVT stratifies exactly as IVT does, and this file is this ladder's row 3:
//!
//! 1. **Row 1** (`CReal.bounded_of_uniformly_continuous`, kernel side): a
//!    *computed* bound on an arbitrary uniformly continuous `F`, never
//!    `∃ K`.
//! 2. **Row 2** (kernel side, **LANDED** 2026-08-27 as
//!    `CReal.evt_attained_max_decides_sign`,
//!    [`creal/extreme_value.rs`](../../../axeyum-lean-kernel/src/creal/extreme_value.rs),
//!    commit `cf77a1912`): attainment is refuted as
//!    constructively unavailable for arbitrary uniformly continuous `F` —
//!    finding *where* the max occurs needs deciding real comparisons, exactly
//!    what [`creal/ivt.rs`](../../../axeyum-lean-kernel/src/creal/ivt.rs)
//!    refutes for roots (there is no `lt_total` on `CReal.lt`). Concretely:
//!    an attained maximum of `t ↦ t·v` on `[0, 1]` yields
//!    `∀ v, v ≤ 0 ∨ 0 ≤ v` — analytic LLPO, the comparison the order
//!    deliberately lacks. One bridge remains **labeled** rather than proved
//!    there (that `evtLinear v` is uniformly continuous, i.e. inside
//!    classical EVT's hypothesis class); see that file's own
//!    "ASSERTED here, not proved" section. The refutation itself is proved.
//! 3. **Row 3 (this file)**: for a **polynomial** `p` with rational
//!    coefficients on a closed rational interval `[a, b]`, zero-testing is
//!    decidable, so the maximum is attained at a **nameable algebraic
//!    point**, exactly, axiom-free, executable. Mirrors
//!    [`crate::real_algebraic::polynomial_ivt`] /
//!    [`crate::real_algebraic::verify_ivt_certificate`] — same shape
//!    (certificate struct + independent-re-derivation checker), same "named,
//!    not approximated" answer.
//! 4. Row 4 (labeled import, not attempted here) would be the classical EVT
//!    for arbitrary continuous `F`, imported with visible axiom footprint.
//!
//! ## Why a sibling module rather than extending `real_algebraic.rs`
//!
//! `real_algebraic.rs` is already 850+ lines carrying the `RealAlgebraic`
//! bridge, `algebraic_eq`, `inv`/`div`, and the IVT certificate. This file's
//! logic — differentiate, isolate `p'`'s roots, filter to the interior,
//! compare finitely many candidate values — is a distinct concern with its
//! own degenerate cases and its own completeness argument, and keeping it
//! separate mirrors how `sturm.rs` (isolation) and `algebraic.rs`
//! (`AlgebraicReal`) are already split out from `real_algebraic.rs` by
//! concern. This module reuses `real_algebraic.rs`'s two new exports
//! ([`crate::real_algebraic::algebraic_cmp`] and
//! [`crate::real_algebraic::eval_poly_at_algebraic`]) rather than duplicating
//! them.
//!
//! ## The route (every ingredient already shipped, before this file)
//!
//! 1. **Differentiate**: [`axeyum_ir::poly::rat_derivative`] — exact,
//!    coefficient-by-coefficient (`aᵢ ↦ i·aᵢ`, shifted down one degree), so
//!    there is nothing to certify beyond recomputing it: any checker can
//!    redo the same linear map and compare.
//! 2. **Isolate the critical points**: [`crate::algebraic::real_roots`]
//!    (`factor_univariate_over_q` + `sturm::isolate_real_roots`) on `p'`,
//!    giving every real root of `p'` as an [`AlgebraicReal`] — minimal
//!    polynomial (irreducible over ℚ) + a Sturm-certified isolating
//!    interval. Filtered here to those strictly inside `(a, b)`.
//! 3. **Evaluate and compare**: [`crate::real_algebraic::eval_poly_at_algebraic`]
//!    evaluates `p` at each candidate exactly (as a [`RealAlgebraic`]), and
//!    [`crate::real_algebraic::algebraic_cmp`] compares the results exactly —
//!    no floating point anywhere in the decision.
//! 4. **Return** the maximizing candidate and the maximum value, plus a
//!    certificate that lets a checker redo all of the above from `poly`,
//!    `a`, `b` alone.
//!
//! ## The completeness argument (why the candidate list needs nothing else)
//!
//! `p` is a polynomial, hence differentiable everywhere, hence continuous on
//! the compact interval `[a, b]`; classical real analysis gives a global
//! maximizer `x*`. Either `x*` is an endpoint (`a` or `b`), or `x*` is
//! interior, in which case Fermat's interior-extremum theorem forces
//! `p'(x*) = 0` — `x*` is a critical point. [`crate::algebraic::real_roots`]
//! isolates **every** real root of `p'`, not merely some of them (Sturm's
//! theorem counts sign changes across the *entire* chain, so a root cannot go
//! unlisted without the sign-change count itself being wrong — which
//! [`verify_extremum_certificate`] independently re-derives, see below). So
//! `{a, b} ∪ {interior roots of p'}` is a **finite, complete** set of
//! candidates for `x*`, and the true maximum is `max` of `p` over that finite
//! set. "I compared some points" proves nothing about maximality on its own;
//! "I compared *every* critical point plus both endpoints, and Sturm
//! guarantees that list is exhaustive" does. [`verify_extremum_certificate`]
//! makes the completeness claim falsifiable rather than asserted: it
//! re-isolates `p'`'s roots from scratch and rejects if the recomputed
//! interior set doesn't match the certificate's `critical_points` in size —
//! catching a dropped candidate, not just a wrong one.
//!
//! ## Degenerate cases (must not panic)
//!
//! - **`a == b`**: the "strictly inside `(a, b)`" filter used for critical
//!   points is vacuously empty (`x` can't be `> a` and `< a` at once when
//!   `a == b`), so this falls out of the general code with no special case;
//!   the sole candidate is the point itself.
//! - **`p` constant** (`p'` is the zero polynomial after trimming, i.e.
//!   `poly::rat_derivative` returns an empty coefficient vector): every point
//!   is critical, but that set is infinite and uninteresting (the value is
//!   the same everywhere), so this module does not attempt to enumerate it —
//!   the two endpoints alone already contain a maximizer, by definition of
//!   "constant". `critical_points` is empty by construction and the checker
//!   accepts an empty `critical_points` exactly when `p'` trims to nothing.
//! - **`p'` has no real roots inside `[a, b]`** (either no real roots at
//!   all, or all of them outside the interval): `critical_points` is empty
//!   and the max is decided by the two endpoints alone. Not a special case —
//!   the filter just keeps nothing.
//! - **Repeated roots of `p'`**: [`crate::algebraic::real_roots`] factors `p'`
//!   over ℚ first and isolates each *distinct* irreducible factor once, so a
//!   repeated root of `p'` (e.g. `p' = (x-1)²·(x+3)`) still contributes
//!   exactly one candidate at `x = 1` — square-free reduction is inherited
//!   for free from the shipped isolation pipeline, not re-derived here (see
//!   `repeated_root_of_derivative_is_one_candidate`, below).
//!
//! ## Scope
//!
//! Univariate, **rational** coefficients, closed interval `[a, b]` with
//! **rational** endpoints. Out of scope: higher dimensions, algebraic (not
//! just rational) endpoints, and open intervals — all three would need a
//! different completeness argument (an open interval need not attain its
//! max at all, e.g. `p = x` on `(0, 1)`).
//!
//! ## Cost and the caps it runs into
//!
//! No new degree cap is added here on top of what the underlying primitives
//! already enforce, and deliberately so: this module never produces a
//! *partial* certificate. Every step that can decline
//! (`real_roots`/`factor_univariate_over_q`'s degree-32 cap,
//! `eval_poly_at_algebraic`/`RealAlgebraic::add`/`mul`'s resultant dimension
//! cap `BIG_MAX_SYLVESTER_DIM = 24`) aborts the *entire* [`polynomial_extremum`]
//! call rather than silently omitting the candidate that tripped it — silently
//! dropping a candidate would falsify the completeness claim the certificate
//! exists to make checkable.
//!
//! **Measured** (`cost_curve_by_degree`, `debug` build): `p = -(x²)+4` on
//! `[-3,3]` (degree 2, 3 candidates) ≈ 0.8 ms; `p = x³-3x` on `[-2,2]`
//! (degree 3, irrational critical points, 4 candidates) ≈ 1.3 ms; a degree-5
//! `p` with rational critical points (5 candidates) ≈ 1.7 ms. The
//! `eval_poly_at_algebraic` mod-reduction trick (see its doc) means the
//! evaluation phase itself stays cheap even at high critical-point degree
//! **when the reduction collapses** — `p = x^n - 2n·x` has `p' = n·(xⁿ⁻¹-2)`
//! (an irreducible degree-`(n-1)` critical point), but `p mod (xⁿ⁻¹-2)`
//! reduces to a single linear term, so evaluation is one multiply-and-add
//! regardless of `n`. What actually dominates that curve
//! (`probe_where_the_decline_actually_happens`, `#[ignore]`d — exploratory,
//! not a committed regression check) is `real_roots`/Sturm isolation of `p'`
//! itself: critical-point degree 4/6/8/10/12/14/16/18/20/22 measured
//! 16–25 ms / 56–87 ms / 153–227 ms / 386–575 ms / 749 ms–1.2 s /
//! 2.5–2.9 s / 2.9 s / 5.1 s / 8.4 s / 13.4–13.7 s — roughly doubling every
//! two degrees of algebraic complexity, the same isolation cost this crate's
//! `real_algebraic.rs` documents elsewhere, inherited here rather than
//! re-derived. At critical-point degree 24 (`n = 25`) that same construction
//! **declines soundly** (`None`, not a panic or a wrong answer) in ~2 ms —
//! fast, because the decline is a cheap up-front check, not an exhausted
//! search.
//!
//! A **"thick"** polynomial (every coefficient nonzero, so `poly mod
//! minimal_poly` does *not* collapse to something small) is markedly more
//! expensive at the *same nominal degree*: measured, `p = Σᵢ₌₀ⁿ (i+1)xⁱ`
//! declined after **~24 s** at `n = 6` (having accepted in 522 ms at `n = 4`
//! and 0.4 ms at `n = 5`, where `p'` happened to have no real roots in
//! range). Isolation cost is driven by the polynomial's coefficient
//! structure, not degree alone — a fair warning against reading the sparse
//! curve above as *the* cost curve for degree `n`.

use core::cmp::Ordering;

use axeyum_ir::{Rational, RealAlgebraic, poly};

use crate::algebraic::AlgebraicReal;
use crate::real_algebraic::{algebraic_cmp, eval_poly_at_algebraic};
use crate::sturm;

/// Where the maximizing candidate lives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtremumLocation {
    /// The left endpoint `a`.
    Left,
    /// The right endpoint `b`.
    Right,
    /// An interior critical point, by index into
    /// [`ExtremumCertificate::critical_points`].
    Critical(usize),
}

/// A checkable certificate for the exact polynomial Extreme Value Theorem:
/// `poly` attains its maximum on `[a, b]` at `argmax`, and `max_value` **is**
/// that maximum, named exactly (as a [`RealAlgebraic`]), not approximated.
///
/// This is *data*, not a trace of the search that found it:
/// [`verify_extremum_certificate`] re-derives every check from `poly`,
/// `deriv`, `a`, `b`, `critical_points`, `argmax`, and `max_value` alone,
/// including re-isolating `deriv`'s roots from scratch to confirm
/// `critical_points` is not missing anything.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtremumCertificate {
    /// The polynomial `p` (LSB-first, rational coefficients).
    pub poly: Vec<Rational>,
    /// `p'`, carried explicitly so the checker can compare it against an
    /// independent recomputation from `poly` (catches a corrupted `poly` or
    /// a corrupted `deriv` — either way the two must still agree).
    pub deriv: Vec<Rational>,
    /// The left interval endpoint.
    pub a: Rational,
    /// The right interval endpoint, with `a <= b`.
    pub b: Rational,
    /// Every real root of `deriv` lying strictly inside `(a, b)` — the
    /// **complete** interior critical-point set (see the module doc's
    /// completeness argument).
    pub critical_points: Vec<AlgebraicReal>,
    /// Which candidate attains the maximum.
    pub argmax: ExtremumLocation,
    /// `poly` evaluated at the `argmax` candidate, exactly.
    pub max_value: RealAlgebraic,
}

/// Produce an [`ExtremumCertificate`] for `poly` on `[a, b]`.
///
/// `None` if `a > b`, if `poly` is empty, or on any underlying
/// differentiation/isolation/arithmetic decline — see the module doc's "Cost
/// and the caps it runs into". A decline here is sound: it never returns a
/// certificate that omits a candidate.
#[must_use]
pub fn polynomial_extremum(
    poly_coeffs: &[Rational],
    a: Rational,
    b: Rational,
) -> Option<ExtremumCertificate> {
    if a.checked_cmp(&b)? == Ordering::Greater {
        return None;
    }
    let trimmed = poly::rat_trim(poly_coeffs.to_vec());
    if trimmed.is_empty() {
        return None; // the zero polynomial: "maximum" is not a meaningful ask
    }
    let deriv = poly::rat_derivative(&trimmed)?;
    let critical_points = interior_critical_points(&deriv, a, b)?;

    // Evaluate every candidate. Any single decline aborts the whole
    // certificate (see module doc) rather than dropping the candidate.
    let value_a = RealAlgebraic::from_rational(poly::eval_rat_poly(&trimmed, a)?)?;
    let value_b = RealAlgebraic::from_rational(poly::eval_rat_poly(&trimmed, b)?)?;

    let mut best_location = ExtremumLocation::Left;
    let mut best_value = value_a;
    if algebraic_cmp(&value_b, &best_value)? == Ordering::Greater {
        best_location = ExtremumLocation::Right;
        best_value = value_b;
    }
    for (idx, root) in critical_points.iter().enumerate() {
        let value = eval_poly_at_algebraic(&trimmed, root)?;
        if algebraic_cmp(&value, &best_value)? == Ordering::Greater {
            best_location = ExtremumLocation::Critical(idx);
            best_value = value;
        }
    }

    Some(ExtremumCertificate {
        poly: trimmed,
        deriv,
        a,
        b,
        critical_points,
        argmax: best_location,
        max_value: best_value,
    })
}

/// Every real root of `deriv` lying strictly inside `(a, b)`.
///
/// `Some(vec![])` when `deriv` trims to the zero polynomial (constant `poly`
/// — see the module doc's degenerate-case list; we do not enumerate the
/// infinite critical set of a constant), when `deriv` is a nonzero constant
/// (no roots at all), or when `deriv` has real roots but none fall inside
/// `(a, b)`. `None` only on an isolation/comparison decline.
fn interior_critical_points(
    deriv: &[Rational],
    a: Rational,
    b: Rational,
) -> Option<Vec<AlgebraicReal>> {
    let trimmed_deriv = poly::rat_trim(deriv.to_vec());
    if trimmed_deriv.is_empty() {
        return Some(Vec::new()); // p is constant; see module doc
    }
    let roots = crate::algebraic::real_roots(&trimmed_deriv)?;
    let mut interior = Vec::new();
    for root in roots {
        if is_strictly_inside(&root, a, b)? {
            interior.push(root);
        }
    }
    Some(interior)
}

/// Whether `root` lies strictly inside `(a, b)`, decided exactly by lifting to
/// a [`RealAlgebraic`] and comparing against both rational endpoints.
fn is_strictly_inside(root: &AlgebraicReal, a: Rational, b: Rational) -> Option<bool> {
    let lifted = crate::real_algebraic::from_algebraic_real(root)?;
    let above_a = lifted.compare_rational(&a)? == Ordering::Greater;
    let below_b = lifted.compare_rational(&b)? == Ordering::Less;
    Some(above_a && below_b)
}

/// Independently re-derive and check an [`ExtremumCertificate`]:
///
/// 1. Recompute `p'` from `poly` and confirm it equals the stored `deriv`.
/// 2. Confirm `a <= b`.
/// 3. For every stored critical point: confirm its minimal polynomial
///    exactly divides `deriv` (it is genuinely a root of the *recomputed*
///    derivative, not some unrelated algebraic number), confirm its
///    isolating interval sits strictly inside `(a, b)`, and **recompute** the
///    Sturm count on that interval to confirm it isolates exactly one root
///    (never trust the stored bracket's own bookkeeping).
/// 4. Confirm the stored critical points are pairwise distinct (so a
///    duplicate cannot be used to pad the count below).
/// 5. **Completeness**: re-isolate `deriv`'s roots from scratch, filter to
///    strictly inside `(a, b)`, and confirm that count equals the stored
///    `critical_points.len()`. Combined with steps 3 and 4 (every stored
///    point is a genuine, distinct interior root of the recomputed `deriv`,
///    and there are exactly as many of them as the *complete* recomputed
///    set), this forces the stored set to equal the true set — a dropped or
///    fabricated candidate changes the count and is rejected.
/// 6. Evaluate every candidate (both endpoints and every critical point)
///    from `poly` alone, confirm `max_value` equals the value at the
///    claimed `argmax` (self-consistency), and confirm `max_value` is `>=`
///    every candidate's value (maximality). Ties are fine either way: this
///    does not require `argmax` to match some canonical choice, only that
///    the claimed value is a genuine tie-or-better everywhere.
///
/// `Some(true)` — valid; `Some(false)` — the certificate is definitely wrong;
/// `None` — declined (overflow/degree cap), never a false accept.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn verify_extremum_certificate(cert: &ExtremumCertificate) -> Option<bool> {
    let ExtremumCertificate {
        poly: poly_coeffs,
        deriv,
        a,
        b,
        critical_points,
        argmax,
        max_value,
    } = cert;

    // Step 1: `deriv` must be exactly the derivative of `poly`.
    let recomputed_deriv = poly::rat_trim(poly::rat_derivative(poly_coeffs)?);
    if recomputed_deriv != poly::rat_trim(deriv.clone()) {
        return Some(false);
    }

    // Step 2.
    let Some(Ordering::Less | Ordering::Equal) = a.checked_cmp(b) else {
        return Some(false);
    };

    // Step 3 + 4: each stored critical point is a genuine, distinct interior
    // root of the recomputed derivative.
    for (i, root) in critical_points.iter().enumerate() {
        if poly::rat_exact_div(&recomputed_deriv, root.minimal_polynomial()).is_none() {
            return Some(false); // not a root of the (recomputed) derivative
        }
        let (lower, upper) = root.isolating_interval();
        if lower.checked_cmp(&upper)? != Ordering::Less {
            return Some(false);
        }
        match sturm::count_real_roots_in(root.minimal_polynomial(), lower, upper) {
            Some(1) => {}
            Some(_) => return Some(false),
            None => return None,
        }
        if is_strictly_inside(root, *a, *b) != Some(true) {
            return Some(false);
        }
        for other in &critical_points[i + 1..] {
            let lifted_i = crate::real_algebraic::from_algebraic_real(root)?;
            let lifted_j = crate::real_algebraic::from_algebraic_real(other)?;
            if crate::real_algebraic::algebraic_eq(&lifted_i, &lifted_j) != Some(false) {
                return Some(false); // duplicate (or an undecided pair): reject
            }
        }
    }

    // Step 5: completeness. Re-isolate from scratch and compare cardinality.
    let recomputed_interior = interior_critical_points(&recomputed_deriv, *a, *b)?;
    if recomputed_interior.len() != critical_points.len() {
        return Some(false);
    }

    // Step 6: evaluate every candidate and check self-consistency +
    // maximality.
    let value_a = RealAlgebraic::from_rational(poly::eval_rat_poly(poly_coeffs, *a)?)?;
    let value_b = RealAlgebraic::from_rational(poly::eval_rat_poly(poly_coeffs, *b)?)?;
    let mut candidate_values = vec![value_a.clone(), value_b.clone()];
    for root in critical_points {
        candidate_values.push(eval_poly_at_algebraic(poly_coeffs, root)?);
    }

    let claimed_value = match *argmax {
        ExtremumLocation::Left => value_a,
        ExtremumLocation::Right => value_b,
        ExtremumLocation::Critical(idx) => {
            let Some(root) = critical_points.get(idx) else {
                return Some(false);
            };
            eval_poly_at_algebraic(poly_coeffs, root)?
        }
    };
    if algebraic_cmp(max_value, &claimed_value)? != Ordering::Equal {
        return Some(false);
    }

    for value in &candidate_values {
        match algebraic_cmp(max_value, value)? {
            Ordering::Less => return Some(false),
            Ordering::Equal | Ordering::Greater => {}
        }
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
    fn interior_max_of_downward_parabola() {
        // p = -(x^2) + 4 on [-3, 3]: max 4 at x = 0 (interior critical point).
        let p = poly_from(&[4, 0, -1]);
        let cert = polynomial_extremum(&p, Rational::integer(-3), Rational::integer(3))
            .expect("must not decline");
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
        assert_eq!(cert.critical_points.len(), 1);
        assert_eq!(cert.argmax, ExtremumLocation::Critical(0));
        assert_eq!(
            cert.critical_points[0].rational_value(),
            Some(Rational::zero())
        );
        assert_eq!(
            cert.max_value.compare_rational(&Rational::integer(4)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn endpoint_max_of_the_identity() {
        // p = x on [0, 2]: max 2 at the endpoint x = 2, no interior critical point.
        let p = poly_from(&[0, 1]);
        let cert = polynomial_extremum(&p, Rational::integer(0), Rational::integer(2))
            .expect("must not decline");
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
        assert!(cert.critical_points.is_empty());
        assert_eq!(cert.argmax, ExtremumLocation::Right);
        assert_eq!(
            cert.max_value.compare_rational(&Rational::integer(2)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn genuine_tie_between_an_interior_point_and_an_endpoint() {
        // p = x^3 - 3x on [-2, 2]: p' = 3x^2 - 3, roots at x = ±1.
        // p(-1) = -1 + 3 = 2, p(1) = 1 - 3 = -2, p(2) = 8 - 6 = 2, p(-2) = -8+6 = -2.
        // Max is 2, attained at BOTH x = -1 (interior) and x = 2 (endpoint) --
        // the case that catches a comparison bug that breaks ties wrong.
        let p = poly_from(&[0, -3, 0, 1]);
        let cert = polynomial_extremum(&p, Rational::integer(-2), Rational::integer(2))
            .expect("must not decline");
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
        assert_eq!(
            cert.max_value.compare_rational(&Rational::integer(2)),
            Some(Ordering::Equal)
        );
        // Whichever candidate the producer picked, it must genuinely tie the
        // other -- confirm both x = -1 and x = 2 evaluate to exactly 2.
        let neg_one = cert
            .critical_points
            .iter()
            .find(|r| r.rational_value() == Some(Rational::integer(-1)))
            .expect("x = -1 must be a listed critical point");
        let value_at_neg_one = eval_poly_at_algebraic(&cert.poly, neg_one).unwrap();
        assert_eq!(
            value_at_neg_one.compare_rational(&Rational::integer(2)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn irrational_argmax() {
        // p = x^3 - 3x^2 on [0, 3]: p' = 3x^2 - 6x = 3x(x-2). Rational roots,
        // so pick a case with a genuinely irrational critical point instead:
        // p = x^3 - 6x on [-3, 3]: p' = 3x^2 - 6, roots at x = +-sqrt(2),
        // irrational. p(-sqrt2) = -2sqrt2 + 6sqrt2 = 4sqrt2 (the interior max
        // on the left branch); compare against the endpoints p(-3) = -27+18 =
        // -9, p(3) = 27 - 18 = 9. 4*sqrt2 ~= 5.657 < 9, so the true max is at
        // the endpoint x = 3 -- exercise the irrational point via a narrower
        // interval that excludes x = 3: [-3, 2].
        let p = poly_from(&[0, -6, 0, 1]);
        let cert = polynomial_extremum(&p, Rational::integer(-3), Rational::integer(2))
            .expect("must not decline");
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
        // The maximizer must be the irrational critical point x = -sqrt(2).
        assert_eq!(cert.argmax, ExtremumLocation::Critical(0));
        let root = &cert.critical_points[0];
        assert_eq!(root.rational_value(), None, "must be irrational");
        assert_eq!(root.degree(), 2);
        // 4*sqrt(2) ~= 5.657: bracket it exactly (no floating point) rather
        // than approximating -- 5 < 4*sqrt(2) < 6.
        assert_eq!(
            cert.max_value.compare_rational(&Rational::integer(5)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            cert.max_value.compare_rational(&Rational::integer(6)),
            Some(Ordering::Less)
        );
    }

    // ---- degenerate cases ----

    #[test]
    fn constant_polynomial_has_no_critical_points() {
        let p = poly_from(&[7]);
        let cert = polynomial_extremum(&p, Rational::integer(-1), Rational::integer(1))
            .expect("must not decline");
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
        assert!(cert.critical_points.is_empty());
        assert_eq!(
            cert.max_value.compare_rational(&Rational::integer(7)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn degenerate_point_interval_does_not_panic() {
        let p = poly_from(&[0, 0, 1]); // x^2
        let cert = polynomial_extremum(&p, Rational::integer(5), Rational::integer(5))
            .expect("must not decline");
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
        assert!(cert.critical_points.is_empty());
        assert_eq!(
            cert.max_value.compare_rational(&Rational::integer(25)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn no_interior_root_in_range_falls_back_to_endpoints() {
        // p = x^2 on [1, 2]: p' = 2x has a root at 0, outside [1, 2].
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_extremum(&p, Rational::integer(1), Rational::integer(2))
            .expect("must not decline");
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
        assert!(cert.critical_points.is_empty());
        assert_eq!(cert.argmax, ExtremumLocation::Right);
    }

    #[test]
    fn repeated_root_of_derivative_is_one_candidate() {
        // p such that p' = (x-1)^2 * (x+3): a repeated root at x = 1 must
        // still contribute exactly one critical-point candidate, not two.
        // (x-1)^2(x+3) = (x^2-2x+1)(x+3) = x^3 + x^2 -5x +3.
        let deriv = poly_from(&[3, -5, 1, 1]);
        assert_eq!(
            poly::rat_degree(&deriv),
            Some(3),
            "sanity: derivative is cubic with a repeated root"
        );
        // Antiderivative (any constant): x^4/4 + x^3/3 - 5x^2/2 + 3x. Scale by
        // 12 to clear denominators: 3x^4 + 4x^3 - 30x^2 + 36x.
        let p = vec![
            Rational::zero(),
            Rational::integer(36),
            Rational::integer(-30),
            Rational::integer(4),
            Rational::integer(3),
        ];
        let recomputed = poly::rat_derivative(&p).unwrap();
        // 12 * deriv, confirming the antiderivative is right.
        let scaled: Vec<Rational> = deriv
            .iter()
            .map(|c| c.checked_mul(Rational::integer(12)).unwrap())
            .collect();
        assert_eq!(poly::rat_trim(recomputed), poly::rat_trim(scaled));

        let cert = polynomial_extremum(&p, Rational::integer(-5), Rational::integer(5))
            .expect("must not decline");
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
        // Roots of p' = 3*(x-1)^2*(x+3) are x=1 (double) and x=-3: two
        // DISTINCT candidates, not three.
        assert_eq!(cert.critical_points.len(), 2);
    }

    // ---- mutation tests: the checker must reject every corruption ----

    fn tie_case_cert() -> ExtremumCertificate {
        let p = poly_from(&[0, -3, 0, 1]); // x^3 - 3x, see genuine_tie test
        polynomial_extremum(&p, Rational::integer(-2), Rational::integer(2))
            .expect("must not decline")
    }

    #[test]
    fn verify_accepts_the_unmutated_control() {
        assert_eq!(verify_extremum_certificate(&tie_case_cert()), Some(true));
    }

    #[test]
    fn verify_rejects_corrupted_polynomial_coefficient() {
        let mut cert = tie_case_cert();
        cert.poly[0] = Rational::integer(5); // x^3 - 3x + 5: deriv no longer matches
        assert_eq!(verify_extremum_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_corrupted_derivative() {
        let mut cert = tie_case_cert();
        cert.deriv[0] = cert.deriv[0].checked_add(Rational::integer(1)).unwrap();
        assert_eq!(verify_extremum_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_swapped_critical_point() {
        let mut cert = tie_case_cert();
        // Swap the critical point x = -1 for an unrelated algebraic number
        // (sqrt(2) in (1, 2)) that is not a root of this p'.
        cert.critical_points[0] = crate::algebraic::test_support::make_unchecked(
            poly_from(&[-2, 0, 1]),
            Rational::integer(1),
            Rational::integer(2),
        );
        assert_eq!(verify_extremum_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_corrupted_bracket() {
        let mut cert = tie_case_cert();
        // Same (correct) minimal polynomial for x = -1 or x = 1, but a
        // bracket that does not isolate it -- and is not even inside (a, b)
        // in a way that would still make it a valid distinct candidate.
        let original = cert.critical_points[0].minimal_polynomial().to_vec();
        cert.critical_points[0] = crate::algebraic::test_support::make_unchecked(
            original,
            Rational::integer(-2),
            Rational::integer(-2),
        );
        assert_eq!(verify_extremum_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_dropped_candidate() {
        // Drop x = -1 (the interior maximizer) from the candidate list. The
        // remaining candidates {x=1, a=-2, b=2} give a WRONG max of p(1) = -2
        // (or the endpoint values), so a checker that only re-checks the
        // *listed* items would not just miss completeness, it must also
        // reject on the self-consistency of the stored `max_value`/`argmax`
        // if those still name the dropped point -- but the interesting case
        // is dropping a candidate that is NOT the argmax, so completeness
        // (not self-consistency) is what has to catch it.
        let mut cert = tie_case_cert();
        assert_eq!(cert.critical_points.len(), 2, "sanity: x = -1 and x = 1");
        // Keep argmax pointing at the OTHER critical point or an endpoint so
        // self-consistency alone would not catch the drop.
        let dropped_is_argmax = cert.argmax == ExtremumLocation::Critical(0);
        cert.critical_points.remove(0); // drops x = -1
        if dropped_is_argmax {
            // Re-point argmax/max_value at the endpoint tie so the only
            // remaining way to reject is the completeness (count) check.
            cert.argmax = ExtremumLocation::Right;
            cert.max_value = RealAlgebraic::from_rational(Rational::integer(2)).unwrap();
        } else {
            // argmax already pointed at index 1 (x = 1); after removing
            // index 0, that candidate is now at index 0. Fix the index so
            // self-consistency alone does not trip (isolate the completeness
            // check as the one doing the rejecting).
            cert.argmax = ExtremumLocation::Critical(0);
        }
        assert_eq!(
            verify_extremum_certificate(&cert),
            Some(false),
            "dropping a real candidate must be caught by the completeness recount"
        );
    }

    #[test]
    fn verify_rejects_a_fabricated_extra_candidate() {
        let mut cert = tie_case_cert();
        // Inject an extra, otherwise-valid critical point (sqrt(2) is NOT a
        // root of this p' = 3x^2-3) padding the count past the true set.
        let roots = crate::algebraic::real_roots(&poly_from(&[-2, 0, 1])).unwrap();
        cert.critical_points.push(roots[0].clone());
        assert_eq!(verify_extremum_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_duplicated_candidate() {
        let mut cert = tie_case_cert();
        let dup = cert.critical_points[0].clone();
        cert.critical_points.push(dup);
        assert_eq!(verify_extremum_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_wrong_argmax_self_consistency() {
        let mut cert = tie_case_cert();
        // Claim the max is at x = 1 (value -2) while max_value still says 2.
        cert.argmax = ExtremumLocation::Critical(
            cert.critical_points
                .iter()
                .position(|r| r.rational_value() == Some(Rational::integer(1)))
                .unwrap(),
        );
        assert_eq!(verify_extremum_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_declines_gracefully_never_panics_on_out_of_range_argmax_index() {
        let mut cert = tie_case_cert();
        cert.argmax = ExtremumLocation::Critical(99);
        assert_eq!(verify_extremum_certificate(&cert), Some(false));
    }

    // ---- boundary-critical-point audit (ADR-1435's open-interval finding,
    // checked against this module: unlike the IVT bridge, endpoints are
    // LEGITIMATE extremum candidates here -- `value_a`/`value_b` are always
    // compared directly -- so this is a completeness question about
    // `critical_points`/`is_strictly_inside`, not a soundness one about the
    // reported maximum. Audited and confirmed clean; these tests pin it. ----

    #[test]
    fn producer_excludes_a_critical_point_sitting_exactly_at_the_left_endpoint() {
        // p = x^2 on [0, 2]: p' = 2x, whose only root x = 0 IS the left
        // endpoint `a` itself. The completeness argument (module doc) says
        // interior candidates are strictly inside (a, b), so this root must
        // not appear in `critical_points` -- the max is decided by the two
        // endpoints alone (p(0) = 0, p(2) = 4).
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_extremum(&p, Rational::integer(0), Rational::integer(2))
            .expect("must not decline");
        assert!(
            cert.critical_points.is_empty(),
            "the boundary root x=0 must not be listed as an interior candidate"
        );
        assert_eq!(cert.argmax, ExtremumLocation::Right);
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
    }

    #[test]
    fn verify_rejects_a_critical_point_forged_exactly_at_the_left_endpoint() {
        // Adversarial: take the clean certificate above and forge in the
        // excluded boundary root as if it were a genuine interior candidate,
        // claiming it as the argmax with the (wrong) value p(0) = 0. Only
        // `is_strictly_inside` (step 3) -- and, independently, the
        // completeness recount (step 5) -- can catch this; there is no
        // incidental unrelated guard doing it by accident here.
        let p = poly_from(&[0, 0, 1]);
        let mut cert = polynomial_extremum(&p, Rational::integer(0), Rational::integer(2))
            .expect("must not decline");
        let boundary_root = crate::algebraic::real_roots(&poly_from(&[0, 1]))
            .unwrap()
            .pop()
            .unwrap();
        assert_eq!(boundary_root.rational_value(), Some(Rational::zero()));
        cert.critical_points = vec![boundary_root];
        cert.argmax = ExtremumLocation::Critical(0);
        cert.max_value = RealAlgebraic::from_rational(Rational::zero()).unwrap();
        assert_eq!(
            verify_extremum_certificate(&cert),
            Some(false),
            "a critical point forged exactly at `a` is not a genuine interior candidate"
        );
    }

    #[test]
    fn producer_excludes_a_critical_point_sitting_exactly_at_the_right_endpoint() {
        // Mirror at `b`: p = x^2 on [-2, 0], p' = 2x, root x = 0 = b.
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_extremum(&p, Rational::integer(-2), Rational::integer(0))
            .expect("must not decline");
        assert!(
            cert.critical_points.is_empty(),
            "the boundary root x=0 must not be listed as an interior candidate"
        );
        assert_eq!(cert.argmax, ExtremumLocation::Left);
        assert_eq!(verify_extremum_certificate(&cert), Some(true));
    }

    #[test]
    fn verify_rejects_a_critical_point_forged_exactly_at_the_right_endpoint() {
        let p = poly_from(&[0, 0, 1]);
        let mut cert = polynomial_extremum(&p, Rational::integer(-2), Rational::integer(0))
            .expect("must not decline");
        let boundary_root = crate::algebraic::real_roots(&poly_from(&[0, 1]))
            .unwrap()
            .pop()
            .unwrap();
        assert_eq!(boundary_root.rational_value(), Some(Rational::zero()));
        cert.critical_points = vec![boundary_root];
        cert.argmax = ExtremumLocation::Critical(0);
        cert.max_value = RealAlgebraic::from_rational(Rational::zero()).unwrap();
        assert_eq!(
            verify_extremum_certificate(&cert),
            Some(false),
            "a critical point forged exactly at `b` is not a genuine interior candidate"
        );
    }

    // ---- cost curve (wall clock; measured, not estimated) ----

    #[test]
    fn cost_curve_by_degree() {
        // Degree 2: p = -(x^2) + 4.
        let d2 = poly_from(&[4, 0, -1]);
        let t0 = Instant::now();
        let c2 = polynomial_extremum(&d2, Rational::integer(-3), Rational::integer(3)).unwrap();
        let e2 = t0.elapsed();
        assert_eq!(verify_extremum_certificate(&c2), Some(true));

        // Degree 3: p = x^3 - 3x (irrational critical points).
        let d3 = poly_from(&[0, -3, 0, 1]);
        let t1 = Instant::now();
        let c3 = polynomial_extremum(&d3, Rational::integer(-2), Rational::integer(2)).unwrap();
        let e3 = t1.elapsed();
        assert_eq!(verify_extremum_certificate(&c3), Some(true));

        // Degree 5: p = x^5 - 5x^3 + 5x + ... chosen so p' factors with
        // small-degree critical points (x^5 - (5/3)x^3): p' = 5x^4 - 5x^2 =
        // 5x^2(x^2-1), roots 0 (double), +-1 -- all RATIONAL, cheap. Scale to
        // clear denominators: p = 3x^5 - 5x^3.
        let d5 = poly_from(&[0, 0, 0, -5, 0, 3]);
        let t2 = Instant::now();
        let c5 = polynomial_extremum(&d5, Rational::integer(-2), Rational::integer(2)).unwrap();
        let e5 = t2.elapsed();
        assert_eq!(verify_extremum_certificate(&c5), Some(true));

        eprintln!(
            "extremum cost curve: deg2={:?} (candidates={}), deg3={:?} (candidates={}), deg5={:?} (candidates={})",
            e2,
            c2.critical_points.len() + 2,
            e3,
            c3.critical_points.len() + 2,
            e5,
            c5.critical_points.len() + 2,
        );
    }

    #[test]
    fn cost_curve_with_a_high_degree_irrational_critical_point_hits_the_resultant_cap() {
        // p' = x^4 - 2 (irreducible, degree-4 real roots +-2^(1/4)) composed
        // against p of degree 5: p = x^5/5 - 2x + ... scaled: p = 5x^5 - 10x
        // has p' = 25x^4 - 10, roots +-(10/25)^(1/4) = +-(2/5)^(1/4), degree 4.
        let p = poly_from(&[0, -10, 0, 0, 0, 5]);
        let t0 = Instant::now();
        let result = polynomial_extremum(&p, Rational::integer(-3), Rational::integer(3));
        let elapsed = t0.elapsed();
        eprintln!(
            "degree-4 critical point (p degree 5) evaluation: {:?}, declined={}",
            elapsed,
            result.is_none()
        );
        // Whichever way this falls (accept or sound decline), it must not
        // panic and it must not silently drop a candidate: if it accepts,
        // the certificate must independently verify.
        if let Some(cert) = result {
            assert_eq!(verify_extremum_certificate(&cert), Some(true));
        }
    }

    #[test]
    #[ignore = "exploratory probe, not part of the committed cost curve"]
    fn probe_where_the_decline_actually_happens() {
        // p' = n*x^(n-1) - 2 for increasing odd n: an irreducible degree-(n-1)
        // critical point evaluated against a degree-n `p`. Used once, by
        // hand, to find where `eval_poly_at_algebraic` actually declines.
        for n in [5usize, 9, 13, 17, 21, 23, 25] {
            // p = x^n - 2n*x, p' = n*(x^(n-1) - 2): x^(n-1)-2 is irreducible
            // (Eisenstein at 2), an irrational critical point of degree n-1.
            let n_i = i128::try_from(n).unwrap();
            let mut coeffs = vec![Rational::zero(); n + 1];
            coeffs[1] = Rational::integer(-2 * n_i);
            coeffs[n] = Rational::integer(1);
            let t0 = Instant::now();
            let result = polynomial_extremum(&coeffs, Rational::integer(-3), Rational::integer(3));
            let elapsed = t0.elapsed();
            eprintln!(
                "sparse n={n}: elapsed={elapsed:?} declined={}",
                result.is_none()
            );
            if let Some(cert) = &result {
                eprintln!(
                    "  critical_points={} degrees={:?}",
                    cert.critical_points.len(),
                    cert.critical_points
                        .iter()
                        .map(super::AlgebraicReal::degree)
                        .collect::<Vec<_>>()
                );
            }
        }

        // A "thick" polynomial (every coefficient nonzero) so `poly mod
        // minimal_poly` does not collapse to something trivial the way the
        // sparse case above does -- isolates whether `eval_poly_at_algebraic`
        // itself (as opposed to isolation/factorization) is the cost driver.
        for degree in [4usize, 5, 6] {
            let coeffs: Vec<Rational> = (0..=degree)
                .map(|i| Rational::integer(i as i128 + 1))
                .collect();
            let t0 = Instant::now();
            let result = polynomial_extremum(&coeffs, Rational::integer(-3), Rational::integer(3));
            let elapsed = t0.elapsed();
            eprintln!(
                "thick degree={degree}: elapsed={elapsed:?} declined={}",
                result.is_none()
            );
            if let Some(cert) = &result {
                eprintln!(
                    "  critical_points={} degrees={:?}",
                    cert.critical_points.len(),
                    cert.critical_points
                        .iter()
                        .map(super::AlgebraicReal::degree)
                        .collect::<Vec<_>>()
                );
            }
        }
    }
}
