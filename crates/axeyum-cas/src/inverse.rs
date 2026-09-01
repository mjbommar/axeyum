//! Exact polynomial INVERSE FUNCTION THEOREM (ADR-0603 row 3): the classical
//! inverse function theorem on the decidable fragment.
//!
//! ## Where this sits in the graded family (ADR-0603; Spivak ch. 12)
//!
//! Spivak's chapter 12 asks three things of an inverse: that it *exists* as a
//! function, that it is *continuous*, and that it is *differentiable*. This
//! repository's chapter-12 row
//! (`docs/curriculum/foundational-books/spivak.md`) records the constructive
//! situation exactly:
//!
//! 1. **Row 1 (constructive general form, landed)** — `CReal`-level order
//!    preservation (`CReal.strict_mono_of_pos_deriv`), conditional order
//!    *reflection* (`CReal.order_reflect_of_pos_deriv`), and the
//!    continuity-of-the-inverse bound
//!    `CReal.inverse_lipschitz_of_pos_deriv`:
//!    `Apart x y → abs (x − y) ≤ (2k+2)·abs (F x − F y)`. That bounds the
//!    domain gap from the codomain gap in both directions — it is genuinely
//!    "the inverse is continuous" — but it never *produces* a domain point.
//! 2. **Row 2 (boundary refutation, landed)** — producing the domain point is
//!    exactly the **exact-root** construction, and that is refuted rather
//!    than merely unbuilt: `crates/axeyum-lean-kernel/src/creal/ivt.rs`
//!    carries two kernel-computed counterexamples (a stationary endpoint
//!    freezes its slack; `F := id` on `[−1, 2]` has the bisection converge to
//!    `1/2` where the root is `0`). So an inverse FUNCTION
//!    `CReal → CReal` is out of reach for a general uniformly continuous `F`,
//!    for a reason that is proved, not asserted.
//! 3. **Row 3 (this file)** — on the decidable fragment the whole classical
//!    statement comes back. For a polynomial `p` with rational coefficients
//!    on a rational interval `[a, b]` with `p'` nowhere zero on `[a, b]`,
//!    and a rational `y` strictly between `p(a)` and `p(b)`, there is a
//!    **unique** `x ∈ (a, b)` with `p(x) = y`, and this file produces that
//!    `x` as a **named** [`AlgebraicReal`] — the exact value of `p⁻¹(y)` —
//!    together with a certificate that re-derives every step.
//! 4. Row 4 (labeled import): not attempted, and there is nothing to attach
//!    it to — `AxReal` axiomatizes an ordered commutative ring with no
//!    completeness axiom, so a classical inverse-function import has no
//!    target (same situation the MVT and LUB families record).
//!
//! This is the fourth sibling of [`crate::real_algebraic::polynomial_ivt`]
//! (IVT), [`crate::extremum::polynomial_extremum`] (EVT),
//! [`crate::mvt::polynomial_mvt`] (MVT) and [`crate::taylor::polynomial_taylor`]
//! (Taylor). It is **not** a restatement of any of them: IVT names *a* root of
//! a sign-changing polynomial and says nothing about how many there are, which
//! is precisely what an inverse cannot tolerate. The mathematical content here
//! is the **uniqueness/well-definedness** half, and it is decided by a Sturm
//! count on the derivative, not by a search.
//!
//! ## The construction
//!
//! Given `p`, rational `a < b`, and rational `y`:
//!
//! 1. Form `p'` (exactly — differentiation of a rational polynomial is exact).
//! 2. Check `p'(a) ≠ 0`, `p'(b) ≠ 0`, and — the decisive step —
//!    **`p'` has no real root in `(a, b]`**, by a Sturm count. Together those
//!    three say `p'` has no zero anywhere on `[a, b]`, hence one strict sign
//!    there, hence `p` is strictly monotone on `[a, b]` and therefore
//!    injective on it. This is the classical hypothesis of the inverse
//!    function theorem, *decided* rather than assumed.
//! 3. Check `y` lies strictly between `p(a)` and `p(b)` (in whichever order
//!    the monotonicity direction puts them). This is the statement that `y`
//!    is in the interior of the range of `p|[a,b]`.
//! 4. Form `q := p − y` and hand it to [`crate::real_algebraic::polynomial_ivt`]
//!    as a black box, exactly as [`crate::mvt`] reuses
//!    [`crate::extremum::polynomial_extremum`]. Step 3 makes `q(a)` and `q(b)`
//!    strictly opposite in sign, so IVT's hypothesis holds by construction;
//!    step 2 makes its answer **unique**, which is what upgrades "a root" to
//!    "the value of the inverse".
//!
//! ## What "independent re-derivation" means here, precisely
//!
//! [`verify_inverse_certificate`] never calls [`polynomial_inverse`]. It
//! recomputes `p'` and `q` from `poly`/`y` with **checker-local**
//! implementations ([`checker_derivative`], [`checker_shift_by`]) that share no
//! code with the producer's `axeyum_ir::poly` routines, in the spirit of
//! `crates/axeyum-cas/src/ntheory_certify.rs` (whose checkers were fixed to use
//! checker-local `gcd`/`lcm` after one was found calling back into its own
//! producer). It then re-runs every decision from `poly`, `a`, `b`, `y` alone.
//!
//! It does share the exact-arithmetic primitives — `Rational`, the Sturm
//! machinery, `AlgebraicReal` — with the producer, and that is a real
//! limitation worth stating rather than papering over: a bug inside Sturm's
//! sign-change counting would be invisible to this checker. That is the same
//! boundary [`crate::real_algebraic::verify_ivt_certificate`] and
//! [`crate::mvt::verify_mvt_certificate`] sit on, and lifting it needs the
//! kernel-reconstruction slice (ADR-0601 §2), not a second CAS checker.
//!
//! **This row is `cas-internal` (ADR-0601): nothing here is reconstructed in
//! the Lean kernel, and it must not be counted as a kernel theorem.**
//!
//! ## Guard classification — MEASURED by deleting each check, not asserted
//!
//! The first version of this section claimed nine independently-falsifiable
//! guards. **That claim was false**, and deleting the checks one at a time in a
//! scratch snapshot is what showed it: of fifteen checks, **twelve survived
//! deletion with all 25 tests still green**, because every fixture corrupted a
//! certificate in a way that several checks reject and whichever one remained
//! caught it. Every fixture was a real test of the checker; none of them was a
//! test of *one* check. That is the exact shape this repository calls a
//! checker that cannot fail, arriving one level down.
//!
//! What the measurement produced, in order:
//!
//! 1. One check was deleted outright. An explicit "`p` is not constant" test
//!    could never fail on its own — a constant `p` has `p' = []`, and
//!    `eval_rat_poly([], a) = 0` makes the endpoint guard reject it anyway.
//! 2. One fixture was rebuilt to isolate the monotonicity guard, which is the
//!    one check that carries this row's actual mathematical content. The
//!    original fixture (`p = x^3 - 3x` on `[1/2, 2]`) did not isolate it:
//!    `p'` has *opposite* signs at those endpoints, so the `deriv_sign` guard
//!    rejects first. The replacement is `[-3/2, 3/2]`, where `p'` is positive
//!    at both ends and vanishes twice strictly inside, `y = 0` is interior to
//!    the range, and `q` genuinely has exactly one root in the bracket
//!    (`+-sqrt 3` fall outside it) — so every other check and every conclusion
//!    re-derivation passes, and deleting the monotonicity count kills that
//!    test and nothing else.
//!
//! Current measured state — **4 of 14 checks are killed by exactly one test**:
//! `deriv` matches the recomputation, `deriv_sign`, the monotonicity Sturm
//! count, and `shifted` matches the recomputation.
//!
//! The other ten are **mutually backing**, and the backup relation was measured
//! too (delete a survivor together with its hypothesised backup and see a test
//! die):
//!
//! | check | backed by | evidence |
//! |---|---|---|
//! | endpoint `p'` nonzero | `deriv_sign` | `signum(0) = 0` never matches a recorded `+-1` |
//! | `y` strictly in range | the `shifted` match, then `minpoly \| q` | a moved `y` makes `q` disagree, then makes the root a non-root |
//! | `minpoly \| q` | the conclusion `p(x) = y` | a root of another polynomial evaluates to the wrong value |
//! | bracket containment | strict interiority | a bracket outside `[a,b]` puts `x` outside `(a,b)` |
//! | `a < b` | seven others together | a swapped interval breaks nearly everything |
//! | bracket recount, point-bracket eval | not reachable | `AlgebraicReal`'s fields are private and every constructor maintains the isolating invariant, so a bad bracket cannot be built through the public API |
//! | uniqueness recount, strict interiority, `p(x) = y` | the guards they back up | each is implied when the others hold |
//!
//! Overlapping checks in a certificate checker are defence in depth and are
//! worth keeping. What is not worth keeping is the *claim* that each one is
//! independently necessary, and that claim is now replaced by the table above.
//!
//! No floating point is used for any decision. (`polynomial_ivt`, reused
//! below, uses an `f64` approximation to *select* which isolated root to name,
//! and then proves the selection by an exact bracket containment — the choice
//! is a heuristic, the acceptance is exact.)

use core::cmp::Ordering;

use axeyum_ir::{Rational, RealAlgebraic, poly};

use crate::algebraic::AlgebraicReal;
use crate::real_algebraic::{algebraic_cmp, eval_poly_at_algebraic};
use crate::sturm;

/// A checkable certificate for the exact polynomial inverse function theorem.
///
/// Every field is redundant with `poly`/`a`/`b`/`y` and is carried so a
/// checker can compare a fresh re-derivation against what the producer
/// claimed, rather than merely recomputing and trusting itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InverseCertificate {
    /// The polynomial `p` (LSB-first, rational coefficients, trimmed).
    pub poly: Vec<Rational>,
    /// The left endpoint of the interval on which `p` is inverted.
    pub a: Rational,
    /// The right endpoint, `a < b`.
    pub b: Rational,
    /// The value being inverted, strictly between `p(a)` and `p(b)`.
    pub y: Rational,
    /// `p'`, LSB-first and trimmed. Nowhere zero on `[a, b]`.
    pub deriv: Vec<Rational>,
    /// The single strict sign of `p'` on `[a, b]`: `1` (`p` increasing) or
    /// `-1` (`p` decreasing). Never `0`.
    pub deriv_sign: i8,
    /// `q := p − y`, LSB-first and trimmed. Its unique root in `(a, b)` is
    /// [`Self::root`].
    pub shifted: Vec<Rational>,
    /// The named exact value `x = p⁻¹(y) ∈ (a, b)`.
    pub root: AlgebraicReal,
}

/// Produce an [`InverseCertificate`] inverting `poly` at `y` over `[a, b]`.
///
/// `None` — a sound decline, never a wrong witness — if `a ≥ b`; if `p` is
/// constant; if `p'` vanishes at `a` or `b` or anywhere in `(a, b]` (the
/// classical hypothesis fails, so `p` need not be injective here); if `y` is
/// not strictly between `p(a)` and `p(b)` (`y` is outside the open range, or
/// is an endpoint value whose preimage is the rational `a` or `b` and should
/// be reported as such rather than through this route); or on any underlying
/// Sturm/isolation/arithmetic decline.
#[must_use]
pub fn polynomial_inverse(
    poly_coeffs: &[Rational],
    a: Rational,
    b: Rational,
    y: Rational,
) -> Option<InverseCertificate> {
    if a.checked_cmp(&b)? != Ordering::Less {
        return None;
    }
    let trimmed = poly::rat_trim(poly_coeffs.to_vec());
    let deriv = poly::rat_derivative(&trimmed)?;
    if deriv.is_empty() {
        // `p` is constant: not injective on any interval, and `p'` is
        // identically zero, so the hypothesis fails in the strongest way.
        return None;
    }

    // Monotonicity, decided: `p'` has no zero on [a, b].
    let d_a = poly::eval_rat_poly(&deriv, a)?;
    let d_b = poly::eval_rat_poly(&deriv, b)?;
    if d_a.is_zero() || d_b.is_zero() {
        return None;
    }
    if d_a.numerator().signum() != d_b.numerator().signum() {
        return None;
    }
    if sturm::count_real_roots_in(&deriv, a, b)? != 0 {
        return None;
    }
    let deriv_sign = i8::try_from(d_a.numerator().signum()).ok()?;

    // `y` strictly inside the range of `p|[a,b]`.
    let pa = poly::eval_rat_poly(&trimmed, a)?;
    let pb = poly::eval_rat_poly(&trimmed, b)?;
    if !strictly_between(y, pa, pb)? {
        return None;
    }

    // The root of `q := p − y`, named by the IVT row-3 route as a black box.
    let shifted = shift_by(&trimmed, y)?;
    let ivt = crate::real_algebraic::polynomial_ivt(&shifted, a, b)?;

    Some(InverseCertificate {
        poly: trimmed,
        a,
        b,
        y,
        deriv,
        deriv_sign,
        shifted,
        root: ivt.root,
    })
}

/// Independently re-derive and check an [`InverseCertificate`].
///
/// Every decision is re-run from `poly`, `a`, `b`, `y` alone; the stored
/// `deriv`, `deriv_sign` and `shifted` are compared against checker-local
/// recomputations rather than trusted. See the module doc for the split
/// between independent guards and the deliberately redundant conclusion
/// re-derivations.
///
/// `Some(true)` — valid; `Some(false)` — the certificate is definitely wrong;
/// `None` — declined (overflow / degree cap), never a false accept.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn verify_inverse_certificate(cert: &InverseCertificate) -> Option<bool> {
    let InverseCertificate {
        poly,
        a,
        b,
        y,
        deriv,
        deriv_sign,
        shifted,
        root,
    } = cert;

    // G1. The interval is a genuine interval.
    let Some(Ordering::Less) = a.checked_cmp(b) else {
        return Some(false);
    };

    // G2. `deriv` is really `p'`, recomputed by a checker-local
    // differentiation that shares no code with the producer's.
    // (There is deliberately no separate "`p` is not constant" guard here.
    // A constant `p` has `p' = []`, `eval_rat_poly([], a) = 0`, and G3 below
    // rejects it — so an explicit emptiness check could never fail on its own,
    // which is exactly the shape this repository treats as worse than no
    // check. Measured: deleting it killed zero tests.)
    let recomputed_deriv = checker_derivative(poly)?;
    if recomputed_deriv != checker_trim(deriv.clone()) {
        return Some(false);
    }

    // G3. `p'` does not vanish at either endpoint.
    let d_a = poly::eval_rat_poly(&recomputed_deriv, *a)?;
    let d_b = poly::eval_rat_poly(&recomputed_deriv, *b)?;
    if d_a.is_zero() || d_b.is_zero() {
        return Some(false);
    }

    // G4. The recorded single sign of `p'` on `[a, b]` is the real one.
    let sign_a = i8::try_from(d_a.numerator().signum()).ok()?;
    let sign_b = i8::try_from(d_b.numerator().signum()).ok()?;
    if *deriv_sign != sign_a || *deriv_sign != sign_b {
        return Some(false);
    }

    // G5. THE monotonicity guard: `p'` has no root in `(a, b]`. With G3 that
    // is "no zero of `p'` anywhere on `[a, b]`", hence `p` is injective there.
    // Dropping this admits a certificate whose root is a genuine root of
    // `q` but is one of several — see `verify_rejects_a_nonmonotone_bracket`.
    match sturm::count_real_roots_in(&recomputed_deriv, *a, *b) {
        Some(0) => {}
        Some(_) => return Some(false),
        None => return None,
    }

    // G6. `y` is strictly interior to the range of `p|[a,b]`.
    let pa = poly::eval_rat_poly(poly, *a)?;
    let pb = poly::eval_rat_poly(poly, *b)?;
    if !strictly_between(*y, pa, pb)? {
        return Some(false);
    }

    // G7. `shifted` is really `p − y`, by a checker-local shift.
    let recomputed_shifted = checker_shift_by(poly, *y)?;
    if recomputed_shifted != checker_trim(shifted.clone()) {
        return Some(false);
    }

    // G8. The named root belongs to `q`: its minimal polynomial must divide
    // `q` exactly. A root lifted in from an unrelated polynomial fails here.
    if poly::rat_exact_div(&recomputed_shifted, root.minimal_polynomial()).is_none() {
        return Some(false);
    }

    // G9. The root's own bracket is a genuine isolating bracket, and it sits
    // inside `[a, b]`. Never trust the bracket's own bookkeeping: recheck it.
    //
    // Two shapes, and the degenerate one is NOT an error.
    // `AlgebraicReal::refine` collapses the bracket to `lower == upper == mid`
    // the moment bisection lands exactly on a rational root (`algebraic.rs`,
    // the `0 =>` arm), so a point bracket is the canonical representation of an
    // exact rational value -- and a Sturm count over the half-open `(x, x]` is
    // then necessarily `0`, never `1`. `verify_ivt_certificate` and
    // `verify_mvt_certificate` both require `lower < upper` and so reject that
    // shape outright: they fail CLOSED, so nothing unsound follows, but they
    // will refuse a correct certificate whose witness happens to be rational
    // and finely refined. Measured here on `p = x^5 + x`, `y = 2` over `[0,2]`,
    // whose witness `x = 1` refines to the bracket `(1, 1]`. This checker
    // handles the case directly rather than inheriting the false negative.
    let (lower, upper) = root.isolating_interval();
    let inside_lower = lower.checked_cmp(a).is_some_and(|o| o != Ordering::Less);
    let inside_upper = upper.checked_cmp(b).is_some_and(|o| o != Ordering::Greater);
    if !inside_lower || !inside_upper {
        return Some(false);
    }
    match lower.checked_cmp(&upper)? {
        Ordering::Greater => return Some(false),
        Ordering::Equal => {
            // Point bracket: the claim is "the root IS the rational `lower`",
            // and the way to check that is to evaluate, not to count.
            if !poly::eval_rat_poly(root.minimal_polynomial(), lower)?.is_zero() {
                return Some(false);
            }
        }
        Ordering::Less => {
            match sturm::count_real_roots_in(root.minimal_polynomial(), lower, upper) {
                Some(1) => {}
                Some(_) => return Some(false),
                None => return None,
            }
        }
    }

    // ---- Conclusion re-derivations (deliberately redundant; see module doc)
    //
    // R1: uniqueness. Implied by G3+G5+G6, recounted anyway because
    // well-definedness of `p⁻¹(y)` is half of what this row claims.
    match sturm::count_real_roots_in(&recomputed_shifted, *a, *b) {
        Some(1) => {}
        Some(_) => return Some(false),
        None => return None,
    }

    // R2: strict interiority. Implied by G6 (which makes `q(a)`, `q(b)`
    // nonzero) together with G9's containment.
    let lifted = crate::real_algebraic::from_algebraic_real(root)?;
    if lifted.compare_rational(a)? != Ordering::Greater
        || lifted.compare_rational(b)? != Ordering::Less
    {
        return Some(false);
    }

    // R3: the conclusion itself, `p(x) = y`, evaluated exactly at the
    // algebraic `x` rather than inferred from `q`'s factorization.
    let p_at_root = eval_poly_at_algebraic(poly, root)?;
    let y_as_algebraic = RealAlgebraic::from_rational(*y)?;
    if algebraic_cmp(&p_at_root, &y_as_algebraic)? != Ordering::Equal {
        return Some(false);
    }

    Some(true)
}

// ============================================================================
// Shared helpers (producer side).
// ============================================================================

/// `true` iff `y` lies strictly between `lo_or_hi` and `hi_or_lo`, in either
/// order. `None` on an incomparable (overflowing) rational pair.
fn strictly_between(y: Rational, p: Rational, q: Rational) -> Option<bool> {
    let (lo, hi) = match p.checked_cmp(&q)? {
        Ordering::Less => (p, q),
        Ordering::Greater => (q, p),
        // `p(a) = p(b)`: the range interior is empty, nothing is strictly
        // between. (Unreachable under the monotonicity guard, but this helper
        // is also called before it in the producer.)
        Ordering::Equal => return Some(false),
    };
    Some(y.checked_cmp(&lo)? == Ordering::Greater && y.checked_cmp(&hi)? == Ordering::Less)
}

/// `p − y`, LSB-first, trimmed. Producer side (uses `axeyum_ir::poly`).
fn shift_by(p: &[Rational], y: Rational) -> Option<Vec<Rational>> {
    let neg_y = vec![Rational::zero().checked_sub(y)?];
    Some(poly::rat_trim(poly::ratpoly_add(p, &neg_y)?))
}

// ============================================================================
// Checker-local re-implementations. These deliberately share no code with the
// producer's `axeyum_ir::poly` routines, so a defect in either differentiation
// or the constant-term shift shows up as a mismatch rather than cancelling.
// ============================================================================

/// Drop trailing zero coefficients (checker-local).
fn checker_trim(mut p: Vec<Rational>) -> Vec<Rational> {
    while p.last().is_some_and(|c| c.is_zero()) {
        p.pop();
    }
    p
}

/// `d/dx` of an LSB-first rational polynomial, trimmed (checker-local).
fn checker_derivative(p: &[Rational]) -> Option<Vec<Rational>> {
    let mut out: Vec<Rational> = Vec::new();
    for (i, coeff) in p.iter().enumerate() {
        if i == 0 {
            continue;
        }
        let k = i128::try_from(i).ok()?;
        // Repeated-addition-free but multiplication-local: build `i` as a
        // rational and multiply, rather than calling the producer's helper.
        out.push(coeff.checked_mul(Rational::new(k, 1))?);
    }
    Some(checker_trim(out))
}

/// `p − y` (checker-local): subtract from the constant coefficient only.
fn checker_shift_by(p: &[Rational], y: Rational) -> Option<Vec<Rational>> {
    let mut out: Vec<Rational> = p.to_vec();
    if out.is_empty() {
        out.push(Rational::zero());
    }
    out[0] = out[0].checked_sub(y)?;
    Some(checker_trim(out))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().map(|&c| Rational::integer(c)).collect()
    }

    fn int(n: i128) -> Rational {
        Rational::integer(n)
    }

    // ---- correctness spot-checks with known answers ----

    #[test]
    fn rational_inverse_of_x_squared() {
        // p = x^2 on [1, 3]: p' = 2x is positive throughout, p(1) = 1,
        // p(3) = 9. Inverting at y = 4 must give exactly x = 2.
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_inverse(&p, int(1), int(3), int(4)).expect("must not decline");
        assert_eq!(verify_inverse_certificate(&cert), Some(true));
        assert_eq!(cert.deriv_sign, 1);
        assert_eq!(cert.root.rational_value(), Some(int(2)));
    }

    #[test]
    fn irrational_inverse_of_x_squared_is_sqrt_two() {
        // Same p, y = 2: the inverse value is sqrt(2), an algebraic number of
        // degree 2 with no rational value at all.
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_inverse(&p, int(1), int(3), int(2)).expect("must not decline");
        assert_eq!(verify_inverse_certificate(&cert), Some(true));
        assert_eq!(cert.root.rational_value(), None);
        assert_eq!(cert.root.degree(), 2);
        // x^2 - 2 is the minimal polynomial, up to a rational scale.
        let m = cert.root.minimal_polynomial();
        assert_eq!(poly::rat_make_monic(m), Some(poly_from(&[-2, 0, 1])));
    }

    #[test]
    fn decreasing_branch_records_a_negative_sign() {
        // p = -x^2 on [1, 3] is strictly DECREASING: p' = -2x < 0.
        // p(1) = -1, p(3) = -9; inverting at y = -4 gives x = 2.
        let p = poly_from(&[0, 0, -1]);
        let cert = polynomial_inverse(&p, int(1), int(3), int(-4)).expect("must not decline");
        assert_eq!(verify_inverse_certificate(&cert), Some(true));
        assert_eq!(cert.deriv_sign, -1);
        assert_eq!(cert.root.rational_value(), Some(int(2)));
    }

    #[test]
    fn a_point_bracket_is_a_real_shape_and_the_sibling_checkers_refuse_it() {
        // MEASURED FINDING, recorded because it is about code this module does
        // NOT own. `AlgebraicReal::refine` collapses its bracket to a single
        // point when bisection lands exactly on a rational root, so `(1, 1]`
        // is a legitimate representation of the value 1 -- and a Sturm count
        // over a half-open `(x, x]` is 0, never 1.
        //
        // `p = x^5 + x` inverted at `y = 2` over `[0, 2]` produces exactly
        // that: the witness is the exact rational 1.
        let p = poly_from(&[0, 1, 0, 0, 0, 1]);
        let cert = polynomial_inverse(&p, int(0), int(2), int(2)).expect("must not decline");
        let (lower, upper) = cert.root.isolating_interval();
        assert_eq!(lower, upper, "the witness refines onto an exact rational");
        assert_eq!(
            sturm::count_real_roots_in(cert.root.minimal_polynomial(), lower, upper),
            Some(0),
            "and a half-open count over a point interval is 0, not 1"
        );

        // This checker accepts it (it evaluates instead of counting)...
        assert_eq!(verify_inverse_certificate(&cert), Some(true));

        // ...while `verify_ivt_certificate`, which requires `lower < upper`,
        // REJECTS the same root on the same polynomial. That is a fail-CLOSED
        // false negative, not an unsoundness: it refuses a correct certificate
        // rather than accepting a wrong one. Pinned here so the sibling
        // checker's behaviour is recorded rather than assumed, and so this
        // test fails loudly if `real_algebraic.rs` is ever fixed (at which
        // point the module doc above needs updating, not this checker).
        let ivt = crate::real_algebraic::IvtCertificate {
            poly: cert.shifted.clone(),
            a: cert.a,
            b: cert.b,
            root: cert.root.clone(),
        };
        assert_eq!(
            crate::real_algebraic::verify_ivt_certificate(&ivt),
            Some(false),
            "sibling checker refuses a point bracket; see this module's G9 note"
        );
    }

    #[test]
    fn quintic_inverse_beyond_radicals() {
        // p = x^5 + x on [0, 2]: p' = 5x^4 + 1 is positive everywhere, so p is
        // globally injective. p(0) = 0, p(2) = 34.
        // y = 2 has the exact rational preimage x = 1 (1 + 1 = 2).
        let p = poly_from(&[0, 1, 0, 0, 0, 1]);
        let cert = polynomial_inverse(&p, int(0), int(2), int(2)).expect("must not decline");
        assert_eq!(verify_inverse_certificate(&cert), Some(true));
        assert_eq!(cert.root.rational_value(), Some(int(1)));

        // y = 3 has an irrational preimage: x^5 + x - 3 has no rational root
        // (the only candidates are +-1, +-3), so the value is a genuine
        // degree-5 algebraic number -- not expressible in radicals in general,
        // and named here regardless.
        let cert3 = polynomial_inverse(&p, int(0), int(2), int(3)).expect("must not decline");
        assert_eq!(verify_inverse_certificate(&cert3), Some(true));
        assert_eq!(cert3.root.rational_value(), None);
        assert_eq!(cert3.root.degree(), 5);
    }

    #[test]
    fn inverse_at_an_algebraic_value_round_trips_through_the_polynomial() {
        // The certificate's own conclusion, checked a second way: evaluate p
        // at the produced root and compare against y exactly.
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_inverse(&p, int(1), int(3), int(5)).expect("must not decline");
        let at = eval_poly_at_algebraic(&cert.poly, &cert.root).expect("evaluates");
        let target = RealAlgebraic::from_rational(int(5)).expect("lifts");
        assert_eq!(algebraic_cmp(&at, &target), Some(Ordering::Equal));
    }

    // ---- the producer declines, soundly, where the hypothesis fails ----

    #[test]
    fn declines_when_the_derivative_vanishes_inside() {
        // p = x^3 - 3x on [-2, 2]: p' = 3x^2 - 3 vanishes at x = +-1, both
        // interior. p is NOT injective here (p(0) = 0 = p(+-sqrt 3)), so the
        // inverse is not a function and the producer must decline.
        let p = poly_from(&[0, -3, 0, 1]);
        assert_eq!(polynomial_inverse(&p, int(-2), int(2), int(0)), None);
    }

    #[test]
    fn declines_when_the_derivative_vanishes_at_an_endpoint() {
        // p = x^2 on [0, 3]: p is injective here, but p'(0) = 0, so the
        // classical hypothesis (nowhere-vanishing derivative) fails and this
        // route declines rather than silently widening its own statement.
        let p = poly_from(&[0, 0, 1]);
        assert_eq!(polynomial_inverse(&p, int(0), int(3), int(4)), None);
    }

    #[test]
    fn declines_on_a_constant_polynomial() {
        let p = poly_from(&[7]);
        assert_eq!(polynomial_inverse(&p, int(0), int(1), int(7)), None);
    }

    #[test]
    fn declines_when_y_is_outside_the_range() {
        // p = x^2 on [1, 3] has range [1, 9]; y = 100 is outside.
        let p = poly_from(&[0, 0, 1]);
        assert_eq!(polynomial_inverse(&p, int(1), int(3), int(100)), None);
    }

    #[test]
    fn declines_when_y_is_an_endpoint_value() {
        // y = p(a) exactly: the preimage is the rational endpoint a, which is
        // not an interior inverse value. Declined rather than reported.
        let p = poly_from(&[0, 0, 1]);
        assert_eq!(polynomial_inverse(&p, int(1), int(3), int(1)), None);
        assert_eq!(polynomial_inverse(&p, int(1), int(3), int(9)), None);
    }

    #[test]
    fn declines_on_a_backwards_interval() {
        let p = poly_from(&[0, 0, 1]);
        assert_eq!(polynomial_inverse(&p, int(3), int(1), int(4)), None);
    }

    // ---- the checker rejects corrupted certificates (one guard each) ----

    fn good_cert() -> InverseCertificate {
        let p = poly_from(&[0, 0, 1]);
        polynomial_inverse(&p, int(1), int(3), int(4)).expect("must not decline")
    }

    #[test]
    fn verify_rejects_a_backwards_interval() {
        // G1
        let mut cert = good_cert();
        core::mem::swap(&mut cert.a, &mut cert.b);
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_corrupted_derivative() {
        // G2
        let mut cert = good_cert();
        cert.deriv = poly_from(&[0, 3]); // claims p' = 3x, really 2x
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_vanishing_endpoint_derivative() {
        // G3. Hand-built (the producer refuses to make one): p = x^2 on
        // [0, 3], where p'(0) = 0, with everything else honest -- x = 2 IS
        // the unique preimage of 4 here, so only the endpoint guard rejects.
        let p = poly_from(&[0, 0, 1]);
        let honest = polynomial_inverse(&p, int(1), int(3), int(4)).expect("must not decline");
        let cert = InverseCertificate {
            a: int(0),
            ..honest
        };
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_wrong_derivative_sign() {
        // G4
        let mut cert = good_cert();
        cert.deriv_sign = -1;
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_nonmonotone_bracket() {
        // A non-monotone bracket with an otherwise-honest witness: p = x^3 - 3x,
        // y = 0 on [1/2, 2], witness sqrt(3). The root is genuine, strictly
        // interior, correctly bracketed, and the UNIQUE root of p in (1/2, 2].
        //
        // CORRECTION, measured by guard deletion: this fixture does NOT isolate
        // G5, and the comment here used to claim it did. `p'(1/2) = -9/4` and
        // `p'(2) = 9` have OPPOSITE signs, so G4 rejects the certificate first
        // and deleting G5 leaves this test green. The isolating fixture is
        // `verify_rejects_a_nonmonotone_bracket_that_every_other_check_accepts`
        // below, on `[-3/2, 3/2]`. This case is kept because a sign-flipping
        // bracket is a distinct and realistic corruption, but it is a test of
        // the checker, not of one check.
        let p = poly_from(&[0, -3, 0, 1]);
        // Build the honest root by the IVT route directly.
        let ivt = crate::real_algebraic::polynomial_ivt(&p, Rational::new(1, 2), int(2))
            .expect("sqrt 3 is bracketed by a sign change here");
        let deriv = poly::rat_derivative(&p).expect("differentiates");
        let cert = InverseCertificate {
            poly: p,
            a: Rational::new(1, 2),
            b: int(2),
            y: int(0),
            deriv,
            deriv_sign: 1,
            shifted: poly_from(&[0, -3, 0, 1]),
            root: ivt.root,
        };
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_nonmonotone_bracket_that_every_other_check_accepts() {
        // G5, ISOLATED. This is the adversarial fixture the guard-deletion run
        // demanded: a certificate over a genuinely satisfiable instance in
        // which every single other check -- and every conclusion
        // re-derivation -- passes, so that deleting G5 makes this test die and
        // nothing else does.
        //
        // `p = x^3 - 3x` on `[-3/2, 3/2]`, `y = 0`.
        //   - `p' = 3x^2 - 3` is POSITIVE at both endpoints (3(9/4) - 3 = 15/4)
        //     so the recorded sign is consistent -- G4 passes -- while `p'`
        //     vanishes at BOTH `x = -1` and `x = 1`, strictly inside. `p` runs
        //     up to `p(-1) = 2`, back down to `p(1) = -2`, then up again: not
        //     injective, so `p^-1` is not a function on this interval at all.
        //   - `y = 0` still lies strictly between `p(-3/2) = 9/8` and
        //     `p(3/2) = -9/8`, so G6 passes.
        //   - `x^3 - 3x = 0` has roots `0` and `+-sqrt 3`, and `sqrt 3 ~ 1.732`
        //     is OUTSIDE `[-3/2, 3/2]`. So `q` has exactly ONE root in the
        //     bracket and the uniqueness recount R1 passes too -- the point
        //     statement "`p(0) = 0`" is perfectly true. What is false is the
        //     claim the certificate makes: that this names the value of an
        //     inverse.
        //
        // My earlier fixture (`[1/2, 2]`, witness `sqrt 3`) does NOT isolate
        // G5: `p'` has opposite signs at those endpoints, so G4 rejects it
        // first and deleting G5 changed nothing. Measured, not assumed.
        let p = poly_from(&[0, -3, 0, 1]);
        let lo = Rational::new(-3, 2);
        let hi = Rational::new(3, 2);

        // The producer refuses outright -- it runs the same Sturm count.
        assert_eq!(polynomial_inverse(&p, lo, hi, int(0)), None);

        let ivt = crate::real_algebraic::polynomial_ivt(&p, lo, hi)
            .expect("q changes sign across [-3/2, 3/2]");
        assert_eq!(ivt.root.rational_value(), Some(int(0)));
        let deriv = poly::rat_derivative(&p).expect("differentiates");
        let cert = InverseCertificate {
            poly: p.clone(),
            a: lo,
            b: hi,
            y: int(0),
            deriv,
            deriv_sign: 1,
            shifted: p,
            root: ivt.root,
        };
        assert_eq!(verify_inverse_certificate(&cert), Some(false));

        // Non-vacuity of the fixture's own premises, so a future edit that
        // makes some OTHER guard reject it silently cannot go unnoticed: the
        // instance really does have a single preimage and a consistent
        // derivative sign, and the derivative really does vanish inside.
        assert_eq!(
            sturm::count_real_roots_in(&cert.shifted, lo, hi),
            Some(1),
            "exactly one preimage of y = 0 in the bracket: R1 must pass"
        );
        assert_eq!(
            sturm::count_real_roots_in(&cert.deriv, lo, hi),
            Some(2),
            "and p' vanishes twice inside it: only G5 can see that"
        );
        assert_eq!(
            poly::eval_rat_poly(&cert.deriv, lo)
                .map(|v| v.numerator().signum())
                .zip(poly::eval_rat_poly(&cert.deriv, hi).map(|v| v.numerator().signum())),
            Some((1, 1)),
            "p' has the SAME sign at both endpoints, so G4 cannot reject"
        );
    }

    #[test]
    fn verify_rejects_a_y_outside_the_range() {
        // G6
        let mut cert = good_cert();
        cert.y = int(100);
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_corrupted_shift() {
        // G7: `shifted` inconsistent with `poly - y`.
        let mut cert = good_cert();
        cert.shifted = poly_from(&[-5, 0, 1]); // claims p - 5, really p - 4
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_root_of_an_unrelated_polynomial() {
        // G8: sqrt(2) is a perfectly good algebraic number in (1, 3), but its
        // minimal polynomial x^2 - 2 does not divide x^2 - 4.
        let mut cert = good_cert();
        let other = polynomial_inverse(&poly_from(&[0, 0, 1]), int(1), int(3), int(2))
            .expect("must not decline");
        cert.root = other.root;
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_bracket_outside_the_interval() {
        // G9's containment clause. `-2` is a genuine root of `x^2 - 4` with a
        // correct isolating bracket, and its minimal polynomial `x + 2` even
        // divides `shifted` exactly -- so G8 passes and only the containment
        // clause rejects. This fixture is what keeps G9 from being satisfiable
        // by any root of the right polynomial anywhere on the line.
        let mut cert = good_cert();
        let far = crate::real_algebraic::polynomial_ivt(&cert.shifted, int(-3), int(-1))
            .expect("-2 is bracketed by a sign change of x^2 - 4 on (-3, -1)");
        assert_eq!(far.root.rational_value(), Some(int(-2)));
        cert.root = far.root;
        assert_eq!(verify_inverse_certificate(&cert), Some(false));
    }

    #[test]
    fn g9s_recount_clause_is_unrepresentably_false_and_this_records_that() {
        // MEASURED, not assumed: G9's "the bracket isolates exactly one root
        // of the minimal polynomial" clause has NO killing fixture in this
        // suite, and that is not an oversight. `AlgebraicReal`'s three fields
        // are private and its only constructors
        // (`crate::algebraic::real_roots` and `AlgebraicReal::refine`) both
        // maintain the isolating-bracket invariant, so a bracket containing
        // zero or two roots of its own minimal polynomial cannot be built
        // through the public API at all.
        //
        // The clause is kept for the reason `verify_ivt_certificate` and
        // `verify_mvt_certificate` keep theirs: it is a recount that does not
        // trust the stored bookkeeping, and it becomes live the moment a
        // certificate arrives from outside this process (a deserialized
        // artifact, a future kernel-reconstruction slice). What it is NOT is a
        // guard this suite has shown can fail -- and a check whose failure has
        // never been demonstrated is exactly what this repository has been
        // burned by, so it is recorded here rather than silently counted among
        // the guards.
        let cert = good_cert();
        let (lower, upper) = cert.root.isolating_interval();
        assert_eq!(
            sturm::count_real_roots_in(cert.root.minimal_polynomial(), lower, upper),
            Some(1),
            "the invariant the clause re-checks holds by construction"
        );
    }

    // ---- the honest negative result about the redundant re-derivations ----

    #[test]
    fn the_conclusion_rederivations_are_implied_and_this_says_so() {
        // R1 (uniqueness recount), R2 (strict interiority) and R3
        // (`p(x) = y`) are each implied when the guards above them hold, and
        // guard-deletion confirms none of the three is killed on its own.
        // What deletion ALSO showed, and what the module doc's table now
        // records, is that the implication runs both ways: deleting
        // `minpoly | q` leaves R3 to reject, and deleting bracket containment
        // leaves R2 to reject. So these are not passengers -- they are the
        // other half of a mutually-backing set. This test pins the direction
        // that matters here: a certificate passing every guard passes all
        // three.
        let cert = good_cert();
        assert_eq!(verify_inverse_certificate(&cert), Some(true));

        // The one direction that IS observable: uniqueness genuinely fails on
        // a non-monotone bracket for a y with several preimages -- but G5
        // rejects such a certificate first, which is exactly why R1 can never
        // be the sole cause of a rejection.
        let p = poly_from(&[0, -3, 0, 1]);
        assert_eq!(
            sturm::count_real_roots_in(&p, int(-2), int(2)),
            Some(3),
            "x^3 - 3x has three roots in (-2, 2]: y = 0 has three preimages"
        );
        assert_ne!(
            sturm::count_real_roots_in(
                &poly::rat_derivative(&p).expect("differentiates"),
                int(-2),
                int(2)
            ),
            Some(0),
            "and G5 sees it: p' vanishes inside the bracket"
        );
    }

    // ---- checker-local helpers agree with the producer's, and are separate ----

    #[test]
    fn checker_local_derivative_agrees_with_the_producer_helper() {
        for coeffs in [
            vec![1, 2, 3, 4, 5],
            vec![0, 0, 1],
            vec![7],
            vec![],
            vec![0, -3, 0, 1],
        ] {
            let p = poly_from(&coeffs);
            assert_eq!(
                checker_derivative(&p),
                poly::rat_derivative(&p),
                "checker-local derivative must agree on {coeffs:?}"
            );
        }
    }

    #[test]
    fn checker_local_shift_agrees_with_the_producer_helper() {
        for (coeffs, y) in [(vec![1, 2, 3], 4i128), (vec![0, 0, 1], -2), (vec![5], 5)] {
            let p = poly_from(&coeffs);
            assert_eq!(
                checker_shift_by(&p, int(y)),
                shift_by(&p, int(y)),
                "checker-local shift must agree on {coeffs:?} - {y}"
            );
        }
    }
}
