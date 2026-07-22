//! Classical orthogonal polynomial families as exact rational polynomials.
//!
//! Each family is generated from its standard **three-term recurrence** and
//! returned as an ordinary [`CasExpr`] polynomial in a chosen variable, built from
//! the canonical [`MultiPoly`] sum-of-monomials form. The supported families are
//! the two Chebyshev kinds, the Legendre, physicists' Hermite, and Laguerre
//! polynomials:
//!
//! - [`chebyshev_t`] — `T₀ = 1`, `T₁ = x`, `Tₙ = 2x·Tₙ₋₁ − Tₙ₋₂`;
//! - [`chebyshev_u`] — `U₀ = 1`, `U₁ = 2x`, `Uₙ = 2x·Uₙ₋₁ − Uₙ₋₂`;
//! - [`legendre`] — `P₀ = 1`, `P₁ = x`, `n·Pₙ = (2n−1)x·Pₙ₋₁ − (n−1)·Pₙ₋₂`;
//! - [`hermite`] — `H₀ = 1`, `H₁ = 2x`, `Hₙ = 2x·Hₙ₋₁ − 2(n−1)·Hₙ₋₂`;
//! - [`laguerre`] — `L₀ = 1`, `L₁ = 1 − x`, `n·Lₙ = (2n−1−x)·Lₙ₋₁ − (n−1)·Lₙ₋₂`.
//!
//! Like [`crate::series`], generation is a **compute** operation rather than a
//! proof-carrying one: no certificate is attached to the returned polynomial.
//! Correctness is pinned by a fixture-backed test suite that checks the low-degree
//! members against their known closed forms via the crate's certified [`equal`]
//! zero-test.
//!
//! # Exactness and overflow
//!
//! Every step runs on dense, least-significant-first `Vec<Rational>` coefficient
//! vectors (index `i` is the coefficient of `varⁱ`), matching the
//! [`axeyum_ir::poly`] convention. All arithmetic is `checked`, so exact `i128`
//! rational overflow (which the fast-growing Hermite/Laguerre coefficients can
//! reach for large `n`) surfaces as an honest `None`, never a panic or a wrong
//! answer.
//!
//! ```
//! use axeyum_cas::{CasExpr, equal, orthopoly::chebyshev_t, ZeroTest};
//!
//! let x = CasExpr::var("x");
//! // T₂(x) = 2x² − 1.
//! let t2 = chebyshev_t(2, "x").unwrap();
//! let expected = CasExpr::int(2) * x.pow(2) - CasExpr::int(1);
//! assert!(matches!(equal(&t2, &expected), ZeroTest::Certified { equal: true, .. }));
//! ```

use axeyum_ir::{Rational, poly};

use crate::{CasExpr, MultiPoly};

/// Scale every coefficient of a least-significant-first rational polynomial by
/// `factor`, returning `None` on exact `i128` rational overflow.
fn scale(coeffs: &[Rational], factor: Rational) -> Option<Vec<Rational>> {
    coeffs.iter().map(|c| c.checked_mul(factor)).collect()
}

/// Divide every coefficient of a least-significant-first rational polynomial by
/// the nonzero `divisor`, returning `None` on exact `i128` rational overflow.
fn divide(coeffs: &[Rational], divisor: Rational) -> Option<Vec<Rational>> {
    coeffs.iter().map(|c| c.checked_div(divisor)).collect()
}

/// Drive a three-term recurrence of the shape
/// `dₙ·pₙ = (a + b·x)·pₙ₋₁ − cₙ·pₙ₋₂` from the two seed polynomials `seed0`
/// (`p₀`) and `seed1` (`p₁`), returning the coefficient vector of `pₙ`.
///
/// The three families' index-dependent data are supplied as closures evaluated at
/// each step `k` in `2..=n`:
///
/// - `linear_multiplier(k)` yields `[a, b]`, the constant and `x` coefficients of
///   the degree-1 factor multiplying `pₖ₋₁`;
/// - `prev2_coefficient(k)` yields `cₖ`, the scalar subtracted times `pₖ₋₂`;
/// - `normalizer(k)` yields `dₖ`, the scalar the whole right-hand side is divided
///   by (`1` when the recurrence is already monic in `pₖ`).
///
/// Each closure returns `Option` so an index-to-rational conversion that overflows
/// declines the whole computation. Returns `None` on any overflow.
fn three_term_recurrence<Multiplier, Prev2, Normalizer>(
    n: u32,
    seed0: &[Rational],
    seed1: &[Rational],
    linear_multiplier: Multiplier,
    prev2_coefficient: Prev2,
    normalizer: Normalizer,
) -> Option<Vec<Rational>>
where
    Multiplier: Fn(u32) -> Option<[Rational; 2]>,
    Prev2: Fn(u32) -> Option<Rational>,
    Normalizer: Fn(u32) -> Option<Rational>,
{
    if n == 0 {
        return Some(seed0.to_vec());
    }
    if n == 1 {
        return Some(seed1.to_vec());
    }
    let mut prev2 = seed0.to_vec();
    let mut prev1 = seed1.to_vec();
    for k in 2..=n {
        // (a + b·x)·pₖ₋₁.
        let multiplier = linear_multiplier(k)?;
        let raised = poly::ratpoly_mul(&prev1, &multiplier)?;
        // −cₖ·pₖ₋₂.
        let coefficient = prev2_coefficient(k)?;
        let subtracted = scale(&prev2, coefficient.checked_neg()?)?;
        let mut current = poly::ratpoly_add(&raised, &subtracted)?;
        // Divide by dₖ when the recurrence is not already monic in pₖ.
        let divisor = normalizer(k)?;
        if divisor != Rational::integer(1) {
            current = divide(&current, divisor)?;
        }
        prev2 = prev1;
        prev1 = current;
    }
    Some(prev1)
}

/// `2n − 1` as an exact rational, or `None` on `i128` overflow.
fn two_n_minus_one(n: u32) -> Option<Rational> {
    Some(Rational::integer(
        i128::from(n).checked_mul(2)?.checked_sub(1)?,
    ))
}

/// `n − 1` as an exact rational, or `None` on `i128` overflow.
fn n_minus_one(n: u32) -> Option<Rational> {
    Some(Rational::integer(i128::from(n).checked_sub(1)?))
}

/// Convert a least-significant-first rational coefficient vector into the
/// canonical [`CasExpr`] polynomial in `var`.
fn to_expr(coeffs: &[Rational], var: &str) -> CasExpr {
    MultiPoly::from_univariate(var, coeffs).to_expr()
}

/// The Chebyshev polynomial of the first kind `Tₙ(var)`, as an exact rational
/// polynomial.
///
/// Generated by `T₀ = 1`, `T₁ = x`, `Tₙ = 2x·Tₙ₋₁ − Tₙ₋₂`. Returns `None` if
/// exact `i128` rational arithmetic overflows.
#[must_use]
pub fn chebyshev_t(n: u32, var: &str) -> Option<CasExpr> {
    let coeffs = three_term_recurrence(
        n,
        &[Rational::integer(1)],
        &[Rational::zero(), Rational::integer(1)],
        |_k| Some([Rational::zero(), Rational::integer(2)]),
        |_k| Some(Rational::integer(1)),
        |_k| Some(Rational::integer(1)),
    )?;
    Some(to_expr(&coeffs, var))
}

/// The Chebyshev polynomial of the second kind `Uₙ(var)`, as an exact rational
/// polynomial.
///
/// Generated by `U₀ = 1`, `U₁ = 2x`, `Uₙ = 2x·Uₙ₋₁ − Uₙ₋₂`. Returns `None` if
/// exact `i128` rational arithmetic overflows.
#[must_use]
pub fn chebyshev_u(n: u32, var: &str) -> Option<CasExpr> {
    let coeffs = three_term_recurrence(
        n,
        &[Rational::integer(1)],
        &[Rational::zero(), Rational::integer(2)],
        |_k| Some([Rational::zero(), Rational::integer(2)]),
        |_k| Some(Rational::integer(1)),
        |_k| Some(Rational::integer(1)),
    )?;
    Some(to_expr(&coeffs, var))
}

/// The Legendre polynomial `Pₙ(var)`, as an exact rational polynomial.
///
/// Generated by `P₀ = 1`, `P₁ = x`, `n·Pₙ = (2n−1)x·Pₙ₋₁ − (n−1)·Pₙ₋₂`. Returns
/// `None` if exact `i128` rational arithmetic overflows.
#[must_use]
pub fn legendre(n: u32, var: &str) -> Option<CasExpr> {
    let coeffs = three_term_recurrence(
        n,
        &[Rational::integer(1)],
        &[Rational::zero(), Rational::integer(1)],
        |k| Some([Rational::zero(), two_n_minus_one(k)?]),
        n_minus_one,
        |k| Some(Rational::integer(i128::from(k))),
    )?;
    Some(to_expr(&coeffs, var))
}

/// The physicists' Hermite polynomial `Hₙ(var)`, as an exact rational polynomial.
///
/// Generated by `H₀ = 1`, `H₁ = 2x`, `Hₙ = 2x·Hₙ₋₁ − 2(n−1)·Hₙ₋₂`. Returns `None`
/// if exact `i128` rational arithmetic overflows.
#[must_use]
pub fn hermite(n: u32, var: &str) -> Option<CasExpr> {
    let coeffs = three_term_recurrence(
        n,
        &[Rational::integer(1)],
        &[Rational::zero(), Rational::integer(2)],
        |_k| Some([Rational::zero(), Rational::integer(2)]),
        |k| n_minus_one(k)?.checked_mul(Rational::integer(2)),
        |_k| Some(Rational::integer(1)),
    )?;
    Some(to_expr(&coeffs, var))
}

/// The Laguerre polynomial `Lₙ(var)`, as an exact rational polynomial.
///
/// Generated by `L₀ = 1`, `L₁ = 1 − x`, `n·Lₙ = (2n−1−x)·Lₙ₋₁ − (n−1)·Lₙ₋₂`.
/// Returns `None` if exact `i128` rational arithmetic overflows.
#[must_use]
pub fn laguerre(n: u32, var: &str) -> Option<CasExpr> {
    let coeffs = three_term_recurrence(
        n,
        &[Rational::integer(1)],
        &[Rational::integer(1), Rational::integer(-1)],
        |k| Some([two_n_minus_one(k)?, Rational::integer(-1)]),
        n_minus_one,
        |k| Some(Rational::integer(i128::from(k))),
    )?;
    Some(to_expr(&coeffs, var))
}

/// The **generalized (associated) Laguerre polynomial** `Lₙ^{(α)}(var)` for a
/// rational parameter `alpha`, from `k·Lₖ = (2k−1+α−x)·Lₖ₋₁ − (k−1+α)·Lₖ₋₂` with
/// `L₀ = 1`, `L₁ = 1 + α − x`. Reduces to [`laguerre`] at `α = 0`; orthogonal on
/// `[0,∞)` with weight `xᵅe^{−x}` (hydrogen radial wavefunctions). `None` on overflow.
pub fn generalized_laguerre(n: u32, alpha: Rational, var: &str) -> Option<CasExpr> {
    let one_plus_alpha = Rational::integer(1).checked_add(alpha)?;
    let coeffs = three_term_recurrence(
        n,
        &[Rational::integer(1)],
        &[one_plus_alpha, Rational::integer(-1)],
        |k| Some([two_n_minus_one(k)?.checked_add(alpha)?, Rational::integer(-1)]),
        |k| n_minus_one(k)?.checked_add(alpha),
        |k| Some(Rational::integer(i128::from(k))),
    )?;
    Some(to_expr(&coeffs, var))
}

/// The **Gegenbauer (ultraspherical) polynomial** `Cₙ^λ(var)` for a rational
/// parameter `lambda`, from `k·Cₖ = 2(k+λ−1)x·Cₖ₋₁ − (k+2λ−2)·Cₖ₋₂` with `C₀ = 1`,
/// `C₁ = 2λx`. Generalizes several classical families: `λ = 1` is [`chebyshev_u`] and
/// `λ = ½` is [`legendre`]. `None` on overflow.
pub fn gegenbauer(n: u32, lambda: Rational, var: &str) -> Option<CasExpr> {
    let two_lambda = Rational::integer(2).checked_mul(lambda)?;
    let coeffs = three_term_recurrence(
        n,
        &[Rational::integer(1)],
        &[Rational::zero(), two_lambda],
        // 2(k+λ−1) = (2k−1) + (2λ−1).
        |k| {
            let b = two_n_minus_one(k)?.checked_add(two_lambda)?.checked_sub(Rational::integer(1))?;
            Some([Rational::zero(), b])
        },
        // k + 2λ − 2.
        |k| Rational::integer(i128::from(k)).checked_add(two_lambda)?.checked_sub(Rational::integer(2)),
        |k| Some(Rational::integer(i128::from(k))),
    )?;
    Some(to_expr(&coeffs, var))
}

/// The **Jacobi polynomial** `Pₙ^{(α,β)}(var)` for rational parameters `alpha`,
/// `beta` — the most general classical family. `P₀ = 1`, `P₁ = (α−β)/2 +
/// (α+β+2)x/2`, then the standard three-term recurrence. Legendre (`α=β=0`),
/// Gegenbauer, and Chebyshev all specialize from it; orthogonal on `[−1,1]` with
/// weight `(1−x)^α(1+x)^β`. `None` on overflow or a degenerate parameter (a vanishing
/// recurrence denominator).
pub fn jacobi(n: u32, alpha: Rational, beta: Rational, var: &str) -> Option<CasExpr> {
    let two = Rational::integer(2);
    let seed1 = [
        alpha.checked_sub(beta)?.checked_div(two)?,
        alpha.checked_add(beta)?.checked_add(two)?.checked_div(two)?,
    ];
    let coeffs = three_term_recurrence(
        n,
        &[Rational::integer(1)],
        &seed1,
        |k| {
            let kr = Rational::integer(i128::from(k));
            let s = two.checked_mul(kr)?.checked_add(alpha)?.checked_add(beta)?; // 2k+α+β
            let f1 = s.checked_sub(Rational::integer(1))?; // 2k+α+β−1
            let const_term = f1.checked_mul(alpha.checked_mul(alpha)?.checked_sub(beta.checked_mul(beta)?)?)?;
            // (2k+α+β−1)·(2k+α+β)·(2k+α+β−2) = f1·s·(s−2).
            let x_coeff = f1.checked_mul(s)?.checked_mul(s.checked_sub(two)?)?;
            Some([const_term, x_coeff])
        },
        |k| {
            let kr = Rational::integer(i128::from(k));
            let s = two.checked_mul(kr)?.checked_add(alpha)?.checked_add(beta)?;
            two.checked_mul(kr.checked_add(alpha)?.checked_sub(Rational::integer(1))?)?
                .checked_mul(kr.checked_add(beta)?.checked_sub(Rational::integer(1))?)?
                .checked_mul(s)
        },
        |k| {
            let kr = Rational::integer(i128::from(k));
            let s = two.checked_mul(kr)?.checked_add(alpha)?.checked_add(beta)?;
            two.checked_mul(kr)?
                .checked_mul(kr.checked_add(alpha)?.checked_add(beta)?)?
                .checked_mul(s.checked_sub(two)?)
        },
    )?;
    Some(to_expr(&coeffs, var))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ZeroTest, equal};

    fn var() -> CasExpr {
        CasExpr::var("x")
    }

    /// Assert two `CasExpr` polynomials are equal via the certified zero-test.
    fn assert_equal(actual: &CasExpr, expected: &CasExpr) {
        match equal(actual, expected) {
            ZeroTest::Certified { equal, witness } => {
                assert!(
                    equal,
                    "polynomial mismatch; difference witness = {witness:?}"
                );
            }
            ZeroTest::Unknown => panic!("expected a decidable (Certified) comparison"),
        }
    }

    #[test]
    fn chebyshev_t_low_degree_closed_forms() {
        // T₂ = 2x² − 1.
        let expected_t2 = CasExpr::int(2) * var().pow(2) - CasExpr::int(1);
        assert_equal(&chebyshev_t(2, "x").expect("T₂"), &expected_t2);
        // T₃ = 4x³ − 3x.
        let expected_t3 = CasExpr::int(4) * var().pow(3) - CasExpr::int(3) * var();
        assert_equal(&chebyshev_t(3, "x").expect("T₃"), &expected_t3);
    }

    #[test]
    fn chebyshev_u_low_degree_closed_form() {
        // U₂ = 4x² − 1.
        let expected_u2 = CasExpr::int(4) * var().pow(2) - CasExpr::int(1);
        assert_equal(&chebyshev_u(2, "x").expect("U₂"), &expected_u2);
    }

    #[test]
    fn legendre_low_degree_closed_forms() {
        // P₂ = (3x² − 1)/2.
        let expected_p2 = CasExpr::rat(3, 2) * var().pow(2) - CasExpr::rat(1, 2);
        assert_equal(&legendre(2, "x").expect("P₂"), &expected_p2);
        // P₃ = (5x³ − 3x)/2.
        let expected_p3 = CasExpr::rat(5, 2) * var().pow(3) - CasExpr::rat(3, 2) * var();
        assert_equal(&legendre(3, "x").expect("P₃"), &expected_p3);
    }

    #[test]
    fn hermite_low_degree_closed_forms() {
        // H₂ = 4x² − 2.
        let expected_h2 = CasExpr::int(4) * var().pow(2) - CasExpr::int(2);
        assert_equal(&hermite(2, "x").expect("H₂"), &expected_h2);
        // H₃ = 8x³ − 12x.
        let expected_h3 = CasExpr::int(8) * var().pow(3) - CasExpr::int(12) * var();
        assert_equal(&hermite(3, "x").expect("H₃"), &expected_h3);
    }

    #[test]
    fn laguerre_low_degree_closed_form() {
        // L₂ = (x² − 4x + 2)/2.
        let expected_l2 =
            CasExpr::rat(1, 2) * var().pow(2) - CasExpr::int(2) * var() + CasExpr::int(1);
        assert_equal(&laguerre(2, "x").expect("L₂"), &expected_l2);
    }

    #[test]
    fn boundary_degree_zero_is_one() {
        // Every family starts at the constant 1.
        for value in [
            chebyshev_t(0, "x"),
            chebyshev_u(0, "x"),
            legendre(0, "x"),
            hermite(0, "x"),
            laguerre(0, "x"),
        ] {
            assert_equal(&value.expect("degree-0 member"), &CasExpr::one());
        }
    }

    #[test]
    fn boundary_degree_one_members() {
        // The correct first-degree member of each family.
        assert_equal(&chebyshev_t(1, "x").expect("T₁"), &var());
        assert_equal(
            &chebyshev_u(1, "x").expect("U₁"),
            &(CasExpr::int(2) * var()),
        );
        assert_equal(&legendre(1, "x").expect("P₁"), &var());
        assert_equal(&hermite(1, "x").expect("H₁"), &(CasExpr::int(2) * var()));
        assert_equal(&laguerre(1, "x").expect("L₁"), &(CasExpr::int(1) - var()));
    }

    #[test]
    fn chebyshev_t_recurrence_self_check_at_five() {
        // Rebuild T₅ purely at the CasExpr level from the recurrence
        // Tₖ = 2x·Tₖ₋₁ − Tₖ₋₂ (a code path independent of the internal
        // rational-vector engine) and confirm it matches the direct call.
        let mut prev2 = CasExpr::one(); // T₀
        let mut prev1 = var(); // T₁
        for _ in 2..=5 {
            let next = CasExpr::int(2) * var() * prev1.clone() - prev2.clone();
            prev2 = prev1;
            prev1 = next;
        }
        assert_equal(&chebyshev_t(5, "x").expect("T₅"), &prev1);
    }
}
