//! Exact polynomial TAYLOR'S THEOREM with Lagrange remainder (ADR-0603 row 3,
//! Spivak ch. 20): for a polynomial `p`, a center `a`, and an evaluation point
//! `b`, there exists `ξ` strictly between `a` and `b` with
//!
//! ```text
//! p(b) − T_n(b) = p⁽ⁿ⁺¹⁾(ξ) · (b−a)ⁿ⁺¹ / (n+1)!
//! ```
//!
//! where `T_n` is the degree-`n` Taylor polynomial of `p` about `a`, and `ξ`
//! is produced **named** — as an [`AlgebraicReal`] — not merely asserted to
//! exist.
//!
//! ## Where this sits in the graded family (ADR-0603)
//!
//! Same ladder as [`crate::mvt`] and [`crate::extremum`]: Taylor's theorem
//! with Lagrange remainder is classically proved by repeated (generalized)
//! Rolle, which needs the same real-analysis machinery this project cannot
//! reach constructively for an arbitrary function. But for a **polynomial**
//! `p`, the remainder `p(x) − T_n(x)` is itself a polynomial divisible
//! exactly by `(x−a)ⁿ⁺¹`, `p⁽ⁿ⁺¹⁾` is itself a polynomial, and the equation
//! the witness must satisfy is a polynomial equation with rational
//! coefficients — so zero-testing and root isolation are decidable, and the
//! witness is reachable exactly, axiom-free, executable, row 3 of the same
//! family MVT and EVT occupy.
//!
//! ## Relation to [`crate::mvt`] — reusable only at `n = 0`
//!
//! Taylor's theorem with Lagrange remainder is proved classically by applying
//! Rolle's theorem **`n+1` times** to a suitable auxiliary function (see "The
//! existence argument" below) — [`crate::mvt::polynomial_mvt`] applies it
//! exactly **once**. At `n = 0`, `T_0(x) = p(a)` and the identity collapses to
//! `p(b) − p(a) = p'(ξ)·(b−a)`, which **is** the ordinary Mean Value Theorem
//! exactly — `taylor_n_zero_matches_ordinary_mvt` (below) confirms the two
//! routes agree on a shared example. For any `n ≥ 1` the induction needs
//! `n+1` nested applications of Rolle, which [`crate::mvt::polynomial_mvt`]
//! does not provide, so this module does **not** build on it for the general
//! case: it instead isolates the witness directly as a root of the specific
//! polynomial equation the generalized-Rolle argument guarantees has one (see
//! below) — the same "isolate every real root, then filter to the interior"
//! route [`crate::extremum`] uses for critical points, reused here via
//! [`crate::algebraic::real_roots`] rather than re-derived.
//!
//! ## The construction
//!
//! 1. **Differentiate and evaluate**: for `k = 0, …, n+1`, `p⁽ᵏ⁾(a)/k!` gives
//!    the Taylor coefficients (`k ≤ n`) and, at `k = n+1`, the derivative
//!    polynomial `p⁽ⁿ⁺¹⁾` itself (not evaluated — needed as a polynomial in
//!    `x` for the next step). `T_n(x) = Σ_{k=0}^n [p⁽ᵏ⁾(a)/k!]·(x−a)^k`.
//! 2. **Isolate a candidate**: form `R(x) = p(x) − T_n(x)` and divide it
//!    exactly by `(x−a)ⁿ⁺¹` to get `Q(x)` (this division is exact by
//!    construction — see "The existence argument"). The witness `ξ` must
//!    satisfy `p⁽ⁿ⁺¹⁾(ξ) = (n+1)!·Q(b)`, a polynomial equation in `ξ` with
//!    rational coefficients; [`crate::algebraic::real_roots`] isolates every
//!    real root exactly, and this module filters to those strictly inside
//!    `(a, b)`.
//! 3. **The certificate carries only what the theorem statement needs**:
//!    `poly`, `a`, `b`, `n`, `taylor_poly` (`T_n`), `deriv_np1` (`p⁽ⁿ⁺¹⁾`),
//!    and `ξ` — **not** `Q` or the intermediate `R`, which are producer-side
//!    search machinery, not part of what [`verify_taylor_certificate`] needs
//!    to re-derive. This is the "certificate is data, not a trace of the
//!    search" split [`crate::mvt`] and [`crate::extremum`] already use, taken
//!    one step further: the checker never needs to know *how* `ξ` was found,
//!    only that the headline identity holds and `ξ` is genuinely interior.
//!
//! ## The existence argument (why a root in `(a, b)` is guaranteed)
//!
//! Let `K := Q(b)` (so `R(b) = K·(b−a)ⁿ⁺¹` exactly, by the division above) and
//! form `g(x) := R(x) − K·(x−a)ⁿ⁺¹ = p(x) − T_n(x) − K·(x−a)ⁿ⁺¹`. Then:
//!
//! - `g(a) = 0`: `T_n(a) = p(a)` (the Taylor polynomial matches at the
//!   center) and `(a−a)ⁿ⁺¹ = 0`.
//! - `g(b) = 0`: `R(b) − K·(b−a)ⁿ⁺¹ = K·(b−a)ⁿ⁺¹ − K·(b−a)ⁿ⁺¹ = 0` exactly, by
//!   the choice of `K`.
//! - `g⁽ᵏ⁾(a) = 0` for every `k = 0, …, n`: `R⁽ᵏ⁾(a) = p⁽ᵏ⁾(a) − T_n⁽ᵏ⁾(a) = 0`
//!   for `k ≤ n` (that is the defining property of the Taylor coefficients —
//!   an algebraic fact about how `T_n` was built, not an analytic one), and
//!   `(x−a)ⁿ⁺¹`'s own derivatives up to order `n` vanish at `x = a`.
//!
//! `g(a) = g(b) = 0` gives (Rolle) some `c₁ ∈ (a, b)` with `g'(c₁) = 0`; paired
//! with `g'(a) = 0` that gives some `c₂ ∈ (a, c₁)` with `g''(c₂) = 0`; and so
//! on. After `n+1` applications, some `ξ ∈ (a, b)` has `g⁽ⁿ⁺¹⁾(ξ) = 0`. Since
//! `T_n` has degree `≤ n`, `T_n⁽ⁿ⁺¹⁾ ≡ 0`, and `(x−a)ⁿ⁺¹`'s `(n+1)`-th
//! derivative is the constant `(n+1)!`, so
//! `g⁽ⁿ⁺¹⁾(x) = p⁽ⁿ⁺¹⁾(x) − K·(n+1)!`, and `g⁽ⁿ⁺¹⁾(ξ) = 0` is exactly
//! `p⁽ⁿ⁺¹⁾(ξ) = K·(n+1)! = (n+1)!·Q(b)` — the equation step 2 isolates roots
//! of. So the classical (generalized-Rolle) argument, not merely wishful
//! thinking, guarantees at least one of [`crate::algebraic::real_roots`]'s
//! isolated roots of that equation lies strictly inside `(a, b)`; finding
//! none there despite a completed search is a sound decline (mirrors
//! [`crate::mvt`]'s own "mathematically unreachable... never trust that
//! reasoning at the call site").
//!
//! The certificate itself does **not** need to re-derive this `n+1`-fold
//! Rolle argument to be checkable: [`verify_taylor_certificate`] only needs
//! to confirm, directly and exactly, that the *headline identity* holds at
//! the stored `ξ` and that `ξ` is genuinely interior — the same "certificate
//! is data" split as every sibling module in this ladder.
//!
//! ## Degenerate cases (must not panic)
//!
//! - **`a == b`** (or `a > b`): no interval; [`polynomial_taylor`] declines.
//! - **`n+1 ≥ deg(p)`**: `p⁽ⁿ⁺¹⁾` has degree `≤ 0` (a constant, possibly
//!   zero), and the "isolate a root of `p⁽ⁿ⁺¹⁾(x) − (n+1)!·Q(b)`" equation
//!   collapses to a **constant** identically equal to zero — algebraically,
//!   because `deg(p) ≤ n` makes `T_n = p` exactly (`R ≡ 0`, so `Q ≡ 0`), and
//!   `deg(p) = n+1` exactly makes `p⁽ⁿ⁺¹⁾` the constant `(n+1)!·(leading
//!   coefficient of p)`, which **is** `(n+1)!·Q(b)` for that same reason (see
//!   `boundary_case_n_plus_1_equals_degree_of_p`, below). Either way, the
//!   Lagrange identity holds for **every** `ξ`, not just one — mirroring
//!   [`crate::mvt`]'s "`g' ≡ 0`" branch, this module names the midpoint
//!   `(a+b)/2` as `ξ` rather than attempting to search a vacuous equation.
//!   **This does not make the checker vacuous**: [`verify_taylor_certificate`]
//!   still independently re-derives the headline identity at the stored `ξ`
//!   and still enforces strict interiority, so a certificate that names an
//!   *exterior* point in this branch (e.g. `ξ = a` itself) is still rejected
//!   — see `verify_rejects_an_exterior_witness_in_the_degenerate_branch`.
//! - **`p` the zero polynomial**: falls out of the general code with no
//!   special case (`T_n ≡ 0`, `p⁽ⁿ⁺¹⁾ ≡ 0`, same degenerate branch as above).
//! - **High `n` or high `deg(p)`**: bounded for free by `(n+1)!` needing to
//!   fit `i128` — [`crate::ntheory::factorial`] declines past `33`, and that
//!   decline happens on the **first** iteration of the shared
//!   producer/checker loop that needs it, well before any per-degree search
//!   cost is paid. No separate degree cap is introduced here.
//! - **High algebraic degree of the witness equation, or the underlying
//!   isolation declining** (Sturm's degree cap, the resultant dimension cap
//!   inside evaluation): [`polynomial_taylor`] returns `None` for the whole
//!   certificate, same policy as [`crate::mvt`] — only one witness is ever
//!   needed, so there is nothing to partially report.
//!
//! ## Scope
//!
//! Univariate, rational coefficients, rational center `a` and evaluation
//! point `b` with `a < b` strictly. Same scope as [`crate::mvt`] and
//! [`crate::extremum`], for the same reasons.
//!
//! ## What this does NOT cover
//!
//! - **Non-polynomial `p`** (`sin`, `exp`, `ln`, …): Taylor's theorem for
//!   these needs the classical (non-constructive) generalized MVT this
//!   project cannot certify — Richardson's theorem makes zero-testing over
//!   that richer function class undecidable, which is exactly why this
//!   ladder stops at the polynomial fragment (row 3, not row 4).
//! - **A bound on the remainder** (the usual textbook corollary — "if
//!   `|p⁽ⁿ⁺¹⁾| ≤ M` on `[a,b]` then the error is `≤ M|b−a|ⁿ⁺¹/(n+1)!`"): out
//!   of scope here. This module produces the **exact** identity with a
//!   **named** `ξ`, which is strictly stronger where it applies, but a bound
//!   over a whole interval is a different (and for non-polynomial `p`, often
//!   the only reachable) statement.
//! - **Multivariate Taylor expansion**: out of scope, same reasoning as
//!   [`crate::extremum`]'s single-variable restriction.
//! - **Uniqueness of `ξ`**: the theorem asserts existence of *a* witness, not
//!   that it is the only one; when the witness equation has several roots in
//!   `(a, b)`, [`polynomial_taylor`] reports the smallest (by
//!   [`crate::algebraic::real_roots`]'s deterministic sort), not a
//!   distinguished one.

use core::cmp::Ordering;

use axeyum_ir::{Rational, RealAlgebraic, poly};

use crate::algebraic::AlgebraicReal;
use crate::real_algebraic::{algebraic_cmp, eval_poly_at_algebraic};
use crate::sturm;

/// A checkable certificate for the exact polynomial Taylor's theorem with
/// Lagrange remainder: for `poly` about center `a`, `taylor_poly` **is** the
/// degree-`n` Taylor polynomial, `deriv_np1` **is** `poly⁽ⁿ⁺¹⁾`, and `xi`
/// **is** a point strictly inside `(a, b)` with
/// `poly(b) − taylor_poly(b) = deriv_np1(xi) · (b−a)ⁿ⁺¹ / (n+1)!`, named
/// exactly (as an [`AlgebraicReal`]), not approximated.
///
/// This is *data*, not a trace of the search that found it:
/// [`verify_taylor_certificate`] re-derives every check from `poly`, `a`,
/// `b`, `n`, `taylor_poly`, `deriv_np1`, and `xi` alone — it never sees the
/// intermediate remainder-quotient the producer used to locate `xi` (see the
/// module doc's "The construction", step 3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TaylorCertificate {
    /// The polynomial `p` (LSB-first, rational coefficients, trimmed).
    pub poly: Vec<Rational>,
    /// The center of the Taylor expansion.
    pub a: Rational,
    /// The evaluation point, with `a < b`.
    pub b: Rational,
    /// The Taylor polynomial's degree bound (the "`n`" in `T_n`).
    pub n: usize,
    /// `T_n(x) = Σ_{k=0}^n [p⁽ᵏ⁾(a)/k!]·(x−a)^k`, carried explicitly so the
    /// checker can compare it against an independent recomputation from
    /// `poly`, `a`, `n` (catches a corrupted `poly` or a corrupted
    /// `taylor_poly` — either way the two must still agree).
    pub taylor_poly: Vec<Rational>,
    /// `p⁽ⁿ⁺¹⁾`, the `(n+1)`-th derivative of `poly`, likewise carried
    /// explicitly for the same reason.
    pub deriv_np1: Vec<Rational>,
    /// The named Lagrange-remainder witness, strictly inside `(a, b)`.
    pub xi: AlgebraicReal,
}

/// Build `(T_n, p⁽ⁿ⁺¹⁾)` from `trimmed`, `a`, `n` in one pass: `T_n(x) =
/// Σ_{k=0}^n [p⁽ᵏ⁾(a)/k!]·(x−a)^k`, and the `(n+1)`-th derivative polynomial
/// of `p`. Shared verbatim between [`polynomial_taylor`] and
/// [`verify_taylor_certificate`] (mirrors [`crate::mvt`]'s `build_g`/
/// `build_deriv_g` split) so the two can never silently diverge on how a
/// Taylor polynomial is computed.
///
/// `None` on arithmetic overflow, or once `(n+1)!` no longer fits `i128`
/// ([`crate::ntheory::factorial`]'s own decline past `33`) — the natural
/// bound on how large an `n` this module can support, reached on the first
/// iteration that needs it rather than after doing `n` iterations of work.
fn build_taylor_and_deriv(
    trimmed: &[Rational],
    a: Rational,
    n: usize,
) -> Option<(Vec<Rational>, Vec<Rational>)> {
    let n1 = n.checked_add(1)?;
    let x_minus_a = [a.checked_neg()?, Rational::integer(1)];
    let mut binom_pow: Vec<Rational> = vec![Rational::integer(1)]; // (x-a)^0
    let mut taylor_acc: Vec<Rational> = Vec::new();
    let mut current = trimmed.to_vec(); // p^(0), p^(1), ... as k advances
    let mut deriv_np1 = Vec::new();
    for k in 0..=n1 {
        if k <= n {
            let fact_k = Rational::integer(crate::ntheory::factorial(i128::try_from(k).ok()?)?);
            let val = poly::eval_rat_poly(&current, a)?;
            let c_k = val.checked_div(fact_k)?;
            if !c_k.is_zero() {
                let term: Vec<Rational> = binom_pow
                    .iter()
                    .map(|coeff| coeff.checked_mul(c_k))
                    .collect::<Option<Vec<_>>>()?;
                taylor_acc = poly::rat_trim(poly::ratpoly_add(&taylor_acc, &term)?);
            }
        }
        if k == n1 {
            deriv_np1 = poly::rat_trim(current);
            break;
        }
        current = poly::rat_derivative(&current)?;
        binom_pow = poly::ratpoly_mul(&binom_pow, &x_minus_a)?;
    }
    Some((taylor_acc, deriv_np1))
}

/// `(x − a)^k`, LSB-first. `None` on overflow.
fn pow_binom(a: Rational, k: usize) -> Option<Vec<Rational>> {
    let x_minus_a = [a.checked_neg()?, Rational::integer(1)];
    let mut acc = vec![Rational::integer(1)];
    for _ in 0..k {
        acc = poly::ratpoly_mul(&acc, &x_minus_a)?;
    }
    Some(acc)
}

/// Exact `base^exp`, by repeated squaring (`O(log exp)` multiplications
/// regardless of how large `exp` is) so an enormous exponent declines
/// promptly on overflow rather than looping `exp` times. `None` on overflow.
fn checked_rat_pow(base: Rational, exp: usize) -> Option<Rational> {
    let mut result = Rational::integer(1);
    let mut b = base;
    let mut e = exp;
    while e > 0 {
        if e & 1 == 1 {
            result = result.checked_mul(b)?;
        }
        e >>= 1;
        if e > 0 {
            b = b.checked_mul(b)?;
        }
    }
    Some(result)
}

/// Represent a rational value `c` as a genuine [`AlgebraicReal`], by isolating
/// the (unique) root of its own degree-1 defining polynomial via
/// [`crate::algebraic::real_roots`] — mirrors [`crate::mvt`]'s own private
/// helper of the same shape (not reusable directly: it is module-private
/// there).
fn rational_as_algebraic_real(c: Rational) -> Option<AlgebraicReal> {
    let linear = vec![
        Rational::integer(c.numerator()).checked_neg()?,
        Rational::integer(c.denominator()),
    ];
    let mut roots = crate::algebraic::real_roots(&linear)?;
    roots.pop()
}

/// Produce a [`TaylorCertificate`] for `poly` about center `a`, evaluated at
/// `b`, for Taylor-polynomial degree `n`.
///
/// `None` if `a >= b` (no interval), if `(n+1)!` doesn't fit `i128`, or on any
/// underlying differentiation/isolation/arithmetic decline — see the module
/// doc's "Degenerate cases". A decline here is sound: it never returns a
/// certificate whose witness is wrong or non-interior.
#[must_use]
pub fn polynomial_taylor(
    poly_coeffs: &[Rational],
    a: Rational,
    n: usize,
    b: Rational,
) -> Option<TaylorCertificate> {
    if a.checked_cmp(&b)? != Ordering::Less {
        return None;
    }
    let trimmed = poly::rat_trim(poly_coeffs.to_vec());
    let (taylor_poly, deriv_np1) = build_taylor_and_deriv(&trimmed, a, n)?;
    let n1 = n.checked_add(1)?;

    // Internal search machinery ONLY (not carried in the certificate, see
    // module doc step 3): R = p - T_n, divided exactly by (x-a)^(n+1), gives
    // the target value the witness's p^(n+1) must hit.
    let neg_taylor = poly::ratpoly_neg(&taylor_poly)?;
    let remainder = poly::rat_trim(poly::ratpoly_add(&trimmed, &neg_taylor)?);
    let binom_np1 = pow_binom(a, n1)?;
    let quotient = poly::rat_exact_div(&remainder, &binom_np1)?;
    let qb = poly::eval_rat_poly(&quotient, b)?;
    let fact_n1 = Rational::integer(crate::ntheory::factorial(i128::try_from(n1).ok()?)?);
    let target = fact_n1.checked_mul(qb)?;
    let witness_eqn = poly::rat_trim(poly::ratpoly_add(&deriv_np1, &[target.checked_neg()?])?);

    let xi = if witness_eqn.is_empty() {
        // Degenerate: the equation is identically 0 (deg(p) <= n+1) -- every
        // point of (a, b) is a valid witness. Name the midpoint.
        let mid = a.checked_add(b)?.checked_div(Rational::integer(2))?;
        rational_as_algebraic_real(mid)?
    } else {
        // General case: xi is a real root of witness_eqn strictly inside
        // (a, b) -- guaranteed to exist by the module doc's existence
        // argument.
        let roots = crate::algebraic::real_roots(&witness_eqn)?;
        let mut found = None;
        for root in roots {
            let lifted = crate::real_algebraic::from_algebraic_real(&root)?;
            if lifted.compare_rational(&a)? == Ordering::Greater
                && lifted.compare_rational(&b)? == Ordering::Less
            {
                found = Some(root);
                break;
            }
        }
        found?
    };

    Some(TaylorCertificate {
        poly: trimmed,
        a,
        b,
        n,
        taylor_poly,
        deriv_np1,
        xi,
    })
}

/// Independently re-derive and check a [`TaylorCertificate`]:
///
/// 1. Confirm `a < b`.
/// 2. Recompute `T_n` and `p⁽ⁿ⁺¹⁾` from `poly`/`a`/`n` alone and confirm they
///    match the stored `taylor_poly`/`deriv_np1`.
/// 3. Confirm `xi`'s own bracket genuinely isolates exactly one root of its
///    stated minimal polynomial (never trust the stored bracket's own
///    bookkeeping) — mirrors [`crate::mvt::verify_mvt_certificate`] and
///    [`crate::extremum::verify_extremum_certificate`].
/// 4. Confirm `xi` is **strictly** interior to `(a, b)` — an exterior root of
///    the witness equation is not Taylor's theorem, however good the
///    arithmetic on it looks (see this module's
///    `verify_rejects_an_exterior_root_that_satisfies_the_value_equation`
///    test).
/// 5. Confirm the headline identity itself, re-derived exactly:
///    `poly(b) − T_n(b) = p⁽ⁿ⁺¹⁾(xi) · (b−a)ⁿ⁺¹ / (n+1)!`.
///
/// `Some(true)` — valid; `Some(false)` — the certificate is definitely wrong;
/// `None` — declined (overflow/degree cap), never a false accept.
#[must_use]
pub fn verify_taylor_certificate(cert: &TaylorCertificate) -> Option<bool> {
    let TaylorCertificate {
        poly,
        a,
        b,
        n,
        taylor_poly,
        deriv_np1,
        xi,
    } = cert;

    // Step 1.
    let Some(Ordering::Less) = a.checked_cmp(b) else {
        return Some(false);
    };

    let trimmed = poly::rat_trim(poly.clone());

    // Step 2.
    let (recomputed_taylor, recomputed_dnp1) = build_taylor_and_deriv(&trimmed, *a, *n)?;
    if recomputed_taylor != poly::rat_trim(taylor_poly.clone()) {
        return Some(false);
    }
    if recomputed_dnp1 != poly::rat_trim(deriv_np1.clone()) {
        return Some(false);
    }

    // Step 3.
    let (lower, upper) = xi.isolating_interval();
    if lower.checked_cmp(&upper)? != Ordering::Less {
        return Some(false);
    }
    match sturm::count_real_roots_in(xi.minimal_polynomial(), lower, upper) {
        Some(1) => {}
        Some(_) => return Some(false),
        None => return None,
    }

    // Step 4.
    let lifted_xi = crate::real_algebraic::from_algebraic_real(xi)?;
    let above_a = lifted_xi.compare_rational(a)?;
    let below_b = lifted_xi.compare_rational(b)?;
    if above_a != Ordering::Greater || below_b != Ordering::Less {
        return Some(false);
    }

    // Step 5.
    let pb = poly::eval_rat_poly(&trimmed, *b)?;
    let tb = poly::eval_rat_poly(&recomputed_taylor, *b)?;
    let lhs = pb.checked_sub(tb)?;
    let n1 = n.checked_add(1)?;
    let fact_n1 = Rational::integer(crate::ntheory::factorial(i128::try_from(n1).ok()?)?);
    let width = b.checked_sub(*a)?;
    let width_pow_n1 = checked_rat_pow(width, n1)?;
    let scale = width_pow_n1.checked_div(fact_n1)?;
    let deriv_at_xi = eval_poly_at_algebraic(&recomputed_dnp1, xi)?;
    let rhs = deriv_at_xi.mul(&RealAlgebraic::from_rational(scale)?)?;
    let lhs_alg = RealAlgebraic::from_rational(lhs)?;
    if algebraic_cmp(&rhs, &lhs_alg)? != Ordering::Equal {
        return Some(false);
    }

    Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Rational;

    fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().map(|&c| Rational::integer(c)).collect()
    }

    // ---- correctness spot-checks with known answers ----

    #[test]
    fn cubic_rational_witness_linear_taylor() {
        // p = x^3, a = 0, n = 1 (linear Taylor approx), b = 2.
        // T_1(x) = p(0) + p'(0)*x = 0 (p'(0) = 0). Remainder = p(2) - 0 = 8.
        // Lagrange: p''(xi)/2! * 2^2 = 12*xi/2 = wait -- p'' = 6x, so
        // p''(xi)*4/2 = 12*xi = 8 => xi = 2/3, RATIONAL.
        let p = poly_from(&[0, 0, 0, 1]);
        let cert = polynomial_taylor(&p, Rational::integer(0), 1, Rational::integer(2))
            .expect("must not decline");
        assert_eq!(verify_taylor_certificate(&cert), Some(true));
        assert_eq!(
            cert.taylor_poly,
            Vec::<Rational>::new(),
            "T_1 = 0 identically"
        );
        assert_eq!(
            cert.xi.rational_value(),
            Some(Rational::checked_new(2, 3).unwrap()),
            "xi = 2/3 exactly"
        );
    }

    #[test]
    fn quartic_irrational_witness() {
        // p = x^4, a = 0, n = 1, b = 2.
        // T_1(x) = 0. R(x) = x^4 = (x-0)^2 * x^2, so Q(x) = x^2, Q(2) = 4.
        // p'' = 12x^2 (deriv_np1, n+1=2). Witness eqn: 12x^2 - 2!*4 = 12x^2-8.
        // Roots: x = +-sqrt(2/3), interior root sqrt(2/3) ~= 0.8165 in (0,2).
        let p = poly_from(&[0, 0, 0, 0, 1]);
        let cert = polynomial_taylor(&p, Rational::integer(0), 1, Rational::integer(2))
            .expect("must not decline");
        assert_eq!(verify_taylor_certificate(&cert), Some(true));
        assert_eq!(
            cert.xi.rational_value(),
            None,
            "xi = sqrt(2/3) must be irrational"
        );
        assert_eq!(cert.xi.degree(), 2);
        let lifted = crate::real_algebraic::from_algebraic_real(&cert.xi).unwrap();
        // sqrt(2/3) ~= 0.8165: bracket with 0 < xi < 1.
        assert_eq!(
            lifted.compare_rational(&Rational::integer(0)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            lifted.compare_rational(&Rational::integer(1)),
            Some(Ordering::Less)
        );
    }

    #[test]
    fn taylor_n_zero_matches_ordinary_mvt() {
        // p = x^2 on [0, 2]: crate::mvt's own test (quadratic_rational_witness)
        // finds slope 2 and witness c = 1. At n = 0, Taylor's theorem IS the
        // ordinary MVT: T_0(x) = p(0) = 0, and
        // p(2) - 0 = p'(xi) * 2 => 4 = 2*xi*2 = 4xi => xi = 1.
        let p = poly_from(&[0, 0, 1]);
        let taylor_cert =
            polynomial_taylor(&p, Rational::integer(0), 0, Rational::integer(2)).unwrap();
        assert_eq!(verify_taylor_certificate(&taylor_cert), Some(true));
        assert_eq!(taylor_cert.xi.rational_value(), Some(Rational::integer(1)));

        let mvt_cert =
            crate::mvt::polynomial_mvt(&p, Rational::integer(0), Rational::integer(2)).unwrap();
        assert_eq!(crate::mvt::verify_mvt_certificate(&mvt_cert), Some(true));
        assert_eq!(mvt_cert.c.rational_value(), taylor_cert.xi.rational_value());
    }

    // ---- degenerate cases ----

    #[test]
    fn degenerate_n_plus_1_exceeds_degree_of_p() {
        // p = x^2 (deg 2), n = 2 (n+1 = 3 > 2): T_2 must equal p exactly.
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_taylor(&p, Rational::integer(1), 2, Rational::integer(3))
            .expect("must not decline");
        assert_eq!(verify_taylor_certificate(&cert), Some(true));
        assert_eq!(
            poly::rat_trim(cert.taylor_poly.clone()),
            poly::rat_trim(cert.poly.clone()),
            "T_n = p exactly when n >= deg(p)"
        );
        assert!(poly::rat_trim(cert.deriv_np1.clone()).is_empty());
        assert_eq!(
            cert.xi.rational_value(),
            Some(Rational::integer(2)),
            "midpoint of [1,3]"
        );
    }

    #[test]
    fn boundary_case_n_plus_1_equals_degree_of_p() {
        // p = x^2 (deg 2), n = 1 (n+1 = 2 = deg(p)): p'' = 2 (nonzero
        // constant) for EVERY xi, so this is still the degenerate branch
        // even though deriv_np1 is not identically zero.
        let p = poly_from(&[0, 0, 1]);
        let cert = polynomial_taylor(&p, Rational::integer(0), 1, Rational::integer(2))
            .expect("must not decline");
        assert_eq!(verify_taylor_certificate(&cert), Some(true));
        assert_eq!(
            poly::rat_trim(cert.deriv_np1.clone()),
            vec![Rational::integer(2)]
        );
        assert_eq!(
            cert.xi.rational_value(),
            Some(Rational::integer(1)),
            "midpoint of [0,2]"
        );
    }

    #[test]
    fn zero_polynomial_is_degenerate() {
        let p = poly_from(&[0]);
        let cert = polynomial_taylor(&p, Rational::integer(-1), 3, Rational::integer(4))
            .expect("must not decline");
        assert_eq!(verify_taylor_certificate(&cert), Some(true));
        assert!(poly::rat_trim(cert.taylor_poly.clone()).is_empty());
    }

    #[test]
    fn degenerate_interval_a_equals_b_declines() {
        let p = poly_from(&[0, 0, 1]);
        assert_eq!(
            polynomial_taylor(&p, Rational::integer(5), 1, Rational::integer(5)),
            None
        );
    }

    #[test]
    fn backwards_interval_a_greater_than_b_declines() {
        let p = poly_from(&[0, 0, 1]);
        assert_eq!(
            polynomial_taylor(&p, Rational::integer(2), 1, Rational::integer(0)),
            None
        );
    }

    // ---- mutation tests: the checker must reject every corruption ----

    fn nontrivial_cert() -> TaylorCertificate {
        // p = x^4, a = 0, n = 1, b = 2 (the irrational-witness case above --
        // deliberately the richer case, not a degenerate one).
        let p = poly_from(&[0, 0, 0, 0, 1]);
        polynomial_taylor(&p, Rational::integer(0), 1, Rational::integer(2))
            .expect("must not decline")
    }

    #[test]
    fn verify_accepts_the_unmutated_control() {
        assert_eq!(verify_taylor_certificate(&nontrivial_cert()), Some(true));
    }

    #[test]
    fn verify_rejects_corrupted_taylor_poly() {
        // T_1 = 0 for this p/a; corrupt it to a nonzero constant. Caught only
        // by step 2's recompute-and-compare -- step 5 (the headline check)
        // uses the freshly RECOMPUTED taylor polynomial, not this field, so
        // without step 2 this corruption would be invisible.
        let mut cert = nontrivial_cert();
        cert.taylor_poly = vec![Rational::integer(1)];
        assert_eq!(verify_taylor_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_wrong_remainder_coefficient() {
        // deriv_np1 = p'' = 12x^2 for this p; corrupt the constant term.
        // Caught only by step 2 -- step 5 evaluates the RECOMPUTED
        // deriv_np1 at xi, never the stored (possibly tampered) copy, so
        // this fixture is dead on arrival without step 2's guard.
        let mut cert = nontrivial_cert();
        cert.deriv_np1[0] = cert.deriv_np1[0].checked_add(Rational::integer(1)).unwrap();
        assert_eq!(verify_taylor_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_wrong_witness_unrelated_to_the_equation() {
        // Swap xi for an entirely unrelated algebraic number (sqrt(2),
        // bracketed in (1,2)) that is not a root of 12x^2-8 at all. Caught by
        // step 5, the headline identity.
        let mut cert = nontrivial_cert();
        cert.xi = crate::algebraic::test_support::make_unchecked(
            poly_from(&[-2, 0, 1]),
            Rational::integer(1),
            Rational::integer(2),
        );
        assert_eq!(verify_taylor_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_an_exterior_root_that_satisfies_the_value_equation() {
        // The interesting adversarial case, mirroring crate::mvt's
        // "verify_rejects_an_endpoint_witness": deriv_np1(x) = 12x^2 depends
        // only on x^2, so the NEGATIVE root -sqrt(2/3) satisfies
        // deriv_np1(x) = 8 = target EXACTLY, same as the genuine witness --
        // but it lies outside (0, 2). A checker that only tested the value
        // equation (skipping strict interiority) would wrongly accept it.
        let cert = nontrivial_cert();
        // Sanity: confirm the coincidence first -- the genuine witness's
        // "opposite" really does satisfy the same value equation.
        let neg_xi_poly = cert.xi.minimal_polynomial().to_vec(); // same poly: 3x^2-2 (up to scale) is even
        let (lo, hi) = cert.xi.isolating_interval();
        let exterior = crate::algebraic::test_support::make_unchecked(
            neg_xi_poly,
            hi.checked_neg().unwrap(),
            lo.checked_neg().unwrap(),
        );
        let deriv_np1 = poly::rat_trim(cert.deriv_np1.clone());
        let genuine_val = eval_poly_at_algebraic(&deriv_np1, &cert.xi).unwrap();
        let exterior_val = eval_poly_at_algebraic(&deriv_np1, &exterior).unwrap();
        assert_eq!(
            algebraic_cmp(&genuine_val, &exterior_val),
            Some(Ordering::Equal),
            "sanity: the exterior point satisfies the SAME value equation as the genuine witness"
        );
        // Confirm it is genuinely exterior to (0, 2).
        let lifted = crate::real_algebraic::from_algebraic_real(&exterior).unwrap();
        assert_eq!(
            lifted.compare_rational(&Rational::integer(0)),
            Some(Ordering::Less),
            "sanity: the exterior point really is negative, hence outside (0,2)"
        );

        let mut mutated = cert;
        mutated.xi = exterior;
        assert_eq!(
            verify_taylor_certificate(&mutated),
            Some(false),
            "an exterior root is not Taylor's theorem, however good the arithmetic looks"
        );
    }

    #[test]
    fn verify_rejects_an_exterior_witness_in_the_degenerate_branch() {
        // Degenerate case (n+1 > deg p): every xi in (a,b) works
        // mathematically, but a certificate naming an EXTERIOR point (here,
        // the left endpoint itself) must still be rejected by the strict
        // interiority check -- this is what keeps the degenerate branch from
        // being a vacuous accept-anything path.
        let p = poly_from(&[0, 0, 1]);
        let mut cert = polynomial_taylor(&p, Rational::integer(1), 2, Rational::integer(3))
            .expect("must not decline");
        assert_eq!(verify_taylor_certificate(&cert), Some(true));
        // Replace the midpoint witness with the left endpoint a = 1 itself.
        cert.xi = rational_as_algebraic_real(Rational::integer(1)).unwrap();
        assert_eq!(verify_taylor_certificate(&cert), Some(false));
    }

    #[test]
    fn verify_rejects_a_corrupted_bracket() {
        let mut cert = nontrivial_cert();
        let original = cert.xi.minimal_polynomial().to_vec();
        cert.xi = crate::algebraic::test_support::make_unchecked(
            original,
            Rational::integer(-2),
            Rational::integer(-2),
        );
        assert_eq!(verify_taylor_certificate(&cert), Some(false));
    }
}
