//! Exact polynomial and rational approximation: interpolation and Padé.
//!
//! This module builds interpolants and rational approximants over the exact
//! `Rational` field, so the coefficients are computed without any floating-point
//! error. Three operations are exposed:
//!
//! - [`lagrange_interpolation`] — the unique polynomial of degree `< N` through
//!   `N` sample points `(xᵢ, yᵢ)` with distinct `xᵢ`, returned as a [`CasExpr`];
//! - [`newton_divided_differences`] — the divided-difference coefficients
//!   `f[x₀], f[x₀,x₁], …` of the Newton form of that same interpolant;
//! - [`pade`] / [`pade_fraction`] — the `[m/n]` Padé approximant `P/Q` matching a
//!   given Maclaurin series through order `m + n`, with `deg P ≤ m`, `deg Q ≤ n`,
//!   and the normalization `Q(0) = 1`.
//!
//! Like [`crate::series`] and [`crate::orthopoly`], these are **compute**
//! operations rather than proof-carrying ones: no certificate is attached to the
//! returned expression. Correctness is instead pinned by a fixture-backed test
//! suite that checks each result against its known closed form via the crate's
//! certified [`equal`](crate::equal) zero-test, and (for Padé) by re-expanding the
//! approximant's own Maclaurin series and confirming it matches the input.
//!
//! # Exactness and overflow
//!
//! Every step runs on dense, least-significant-first `Vec<Rational>` coefficient
//! vectors (index `i` is the coefficient of `varⁱ`), matching the
//! [`axeyum_ir::poly`] convention, and every arithmetic operation is `checked`.
//! Exact `i128` rational overflow, a singular Padé denominator system, repeated
//! `xᵢ`, or too few series coefficients all surface as an honest `None` — never a
//! panic or a wrong answer.

use axeyum_ir::{Rational, poly};

use crate::{CasExpr, MultiPoly};

/// Returns `true` iff every abscissa `xᵢ` in `points` is distinct (interpolation
/// is only well posed when the sample points have distinct `x` coordinates).
fn distinct_abscissae(points: &[(Rational, Rational)]) -> bool {
    for (i, (xi, _)) in points.iter().enumerate() {
        for (xj, _) in points.iter().skip(i + 1) {
            if xi == xj {
                return false;
            }
        }
    }
    true
}

/// Expand a polynomial given in **Newton form** — coefficients `coeffs[k]`
/// against the basis `∏_{t<k} (x − xₜ)`, where `xₜ = points[t].0` — into a dense,
/// least-significant-first standard coefficient vector. `None` on exact `i128`
/// rational overflow.
fn newton_form_to_coeffs(
    points: &[(Rational, Rational)],
    coeffs: &[Rational],
) -> Option<Vec<Rational>> {
    let mut result = vec![Rational::zero()];
    // The running Newton basis polynomial ∏_{t<k} (x − xₜ), starting at 1.
    let mut basis = vec![Rational::integer(1)];
    for (coeff, point) in coeffs.iter().zip(points.iter()) {
        let scaled = poly::ratpoly_mul(&basis, &[*coeff])?;
        result = poly::ratpoly_add(&result, &scaled)?;
        // basis ← basis · (x − xₖ).
        let factor = [point.0.checked_neg()?, Rational::integer(1)];
        basis = poly::ratpoly_mul(&basis, &factor)?;
    }
    Some(poly::rat_trim(result))
}

/// The Newton divided-difference coefficients of the interpolant through
/// `points`.
///
/// Given `N` points `(xᵢ, yᵢ)` with distinct `xᵢ`, returns the coefficients
/// `[f[x₀], f[x₀,x₁], …, f[x₀,…,x_{N-1}]]` of the Newton form
/// `f(x) = Σₖ cₖ · ∏_{t<k}(x − xₜ)`. These are exactly the leading coefficients of
/// the successive divided-difference table.
///
/// Returns `None` if `points` is empty, if two abscissae coincide, or on exact
/// `i128` rational overflow.
#[must_use]
pub fn newton_divided_differences(points: &[(Rational, Rational)]) -> Option<Vec<Rational>> {
    if points.is_empty() || !distinct_abscissae(points) {
        return None;
    }
    let count = points.len();
    // Start from the ordinates; refine in place into divided differences.
    let mut coeff: Vec<Rational> = points.iter().map(|p| p.1).collect();
    for level in 1..count {
        for i in (level..count).rev() {
            let num = coeff[i].checked_sub(coeff[i - 1])?;
            let den = points[i].0.checked_sub(points[i - level].0)?;
            coeff[i] = num.checked_div(den)?;
        }
    }
    Some(coeff)
}

/// The unique interpolating polynomial through `points`, as a [`CasExpr`] in
/// `var`.
///
/// Given `N` points `(xᵢ, yᵢ)` with distinct `xᵢ`, returns the unique polynomial
/// of degree `< N` satisfying `p(xᵢ) = yᵢ` for every `i`. The coefficient vector
/// is built exactly over ℚ (via the Newton divided-difference form, which is
/// mathematically identical to the Lagrange interpolant) and then rendered to the
/// canonical expanded sum-of-monomials expression.
///
/// Returns `None` if `points` is empty, if two abscissae coincide, or on exact
/// `i128` rational overflow.
#[must_use]
pub fn lagrange_interpolation(points: &[(Rational, Rational)], var: &str) -> Option<CasExpr> {
    let divided = newton_divided_differences(points)?;
    let coeffs = newton_form_to_coeffs(points, &divided)?;
    Some(MultiPoly::from_univariate(var, &coeffs).to_expr())
}

/// Solve for the `[m/n]` Padé numerator and denominator coefficient vectors.
///
/// Returns `(P, Q)` as dense least-significant-first vectors with `Q[0] = 1`,
/// `deg P ≤ m`, `deg Q ≤ n`, such that `P − Q · A ≡ 0 (mod x^{m+n+1})` where `A`
/// is the series with coefficients `series_coeffs`. `None` if the series supplies
/// fewer than `m + n + 1` coefficients, if the denominator system is singular, or
/// on overflow.
fn pade_coeffs(
    series_coeffs: &[Rational],
    m: usize,
    n: usize,
) -> Option<(Vec<Rational>, Vec<Rational>)> {
    let needed = m.checked_add(n)?.checked_add(1)?;
    if series_coeffs.len() < needed {
        return None;
    }
    // Series coefficient accessor: out-of-range indices read as zero.
    let coeff = |idx: usize| series_coeffs.get(idx).copied().unwrap_or_else(Rational::zero);

    // Denominator unknowns q₁..qₙ solve, for each order k = m+1..=m+n,
    //   Σ_{u=1}^{n} q_u · a_{k-u} = −a_k        (with q₀ = 1).
    // Column `u` of the linear system carries the coefficients of unknown q_u.
    let denom_tail = if n == 0 {
        Vec::new()
    } else {
        let cols: Vec<Vec<Rational>> = (1..=n)
            .map(|unknown| {
                (0..n)
                    .map(|row| {
                        let order = m + 1 + row;
                        order.checked_sub(unknown).map_or_else(Rational::zero, coeff)
                    })
                    .collect()
            })
            .collect();
        let rhs: Vec<Rational> = (0..n)
            .map(|row| coeff(m + 1 + row).checked_neg())
            .collect::<Option<_>>()?;
        crate::ratint::solve_linear(&cols, &rhs)?
    };
    let mut denom = Vec::with_capacity(n + 1);
    denom.push(Rational::integer(1));
    denom.extend(denom_tail);

    // Numerator coefficients p_k = Σ_{u=0}^{min(k,n)} q_u · a_{k-u}, k = 0..=m.
    let mut numer = Vec::with_capacity(m + 1);
    for order in 0..=m {
        let mut acc = Rational::zero();
        for (unknown, qu) in denom.iter().take(order.min(n) + 1).enumerate() {
            let term = qu.checked_mul(coeff(order - unknown))?;
            acc = acc.checked_add(term)?;
        }
        numer.push(acc);
    }

    Some((poly::rat_trim(numer), poly::rat_trim(denom)))
}

/// The `[m/n]` Padé numerator and denominator coefficient vectors of a Maclaurin
/// series.
///
/// Given the Maclaurin coefficients `series_coeffs` (index `i` is the coefficient
/// of `xⁱ`), returns `(P, Q)` as dense least-significant-first coefficient
/// vectors of the `[m/n]` Padé approximant: `deg P ≤ m`, `deg Q ≤ n`, `Q(0) = 1`,
/// and the rational function `P/Q` agrees with the series through order `m + n`
/// (`P − Q · A ≡ 0 (mod x^{m+n+1})`).
///
/// Returns `None` if `series_coeffs` supplies fewer than `m + n + 1` coefficients,
/// if the denominator linear system is singular, or on exact `i128` rational
/// overflow.
#[must_use]
pub fn pade_fraction(
    series_coeffs: &[Rational],
    m: usize,
    n: usize,
) -> Option<(Vec<Rational>, Vec<Rational>)> {
    pade_coeffs(series_coeffs, m, n)
}

/// The `[m/n]` Padé approximant of a Maclaurin series, as a [`CasExpr`] quotient
/// `P(var) / Q(var)`.
///
/// Given the Maclaurin coefficients `series_coeffs` (index `i` is the coefficient
/// of `xⁱ`), returns the rational function `P/Q` with `deg P ≤ m`, `deg Q ≤ n`,
/// `Q(0) = 1`, matching the series through order `m + n`. See [`pade_fraction`]
/// for the raw coefficient vectors.
///
/// Returns `None` under the same conditions as [`pade_fraction`].
#[must_use]
pub fn pade(series_coeffs: &[Rational], m: usize, n: usize, var: &str) -> Option<CasExpr> {
    let (numer, denom) = pade_coeffs(series_coeffs, m, n)?;
    let numer_expr = MultiPoly::from_univariate(var, &numer).to_expr();
    let denom_expr = MultiPoly::from_univariate(var, &denom).to_expr();
    Some(CasExpr::Div(Box::new(numer_expr), Box::new(denom_expr)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ZeroTest, equal};
    use std::collections::BTreeMap;

    /// An integer point/coefficient shorthand.
    fn r(n: i128) -> Rational {
        Rational::integer(n)
    }

    /// Assert that two expressions are certified equal by the crate zero-test.
    fn assert_certified_equal(a: &CasExpr, b: &CasExpr) {
        assert!(
            matches!(equal(a, b), ZeroTest::Certified { equal: true, .. }),
            "expected {a} == {b}",
        );
    }

    #[test]
    fn lagrange_recovers_square() {
        // (0,0), (1,1), (2,4) lie on y = x².
        let points = [(r(0), r(0)), (r(1), r(1)), (r(2), r(4))];
        let got = lagrange_interpolation(&points, "x").unwrap();
        let expected = CasExpr::var("x").pow(2);
        assert_certified_equal(&got, &expected);
    }

    #[test]
    fn lagrange_recovers_square_plus_one() {
        // (0,1), (1,2), (2,5) lie on y = x² + 1.
        let points = [(r(0), r(1)), (r(1), r(2)), (r(2), r(5))];
        let got = lagrange_interpolation(&points, "x").unwrap();
        let expected = CasExpr::var("x").pow(2) + CasExpr::int(1);
        assert_certified_equal(&got, &expected);
    }

    #[test]
    fn lagrange_reproduces_the_points() {
        // A generic degree-3 interpolant through four rational points must
        // evaluate back to each ordinate exactly.
        let points = [
            (Rational::new(-1, 2), r(3)),
            (r(0), Rational::new(1, 3)),
            (r(1), r(7)),
            (r(2), Rational::new(-5, 4)),
        ];
        let got = lagrange_interpolation(&points, "x").unwrap();
        for (x, y) in &points {
            let mut env = BTreeMap::new();
            env.insert("x".to_owned(), *x);
            assert_eq!(got.eval(&env), Some(*y));
        }
    }

    #[test]
    fn newton_divided_differences_of_square() {
        // Divided-difference table of (0,0),(1,1),(2,4): [0, 1, 1].
        let points = [(r(0), r(0)), (r(1), r(1)), (r(2), r(4))];
        let dd = newton_divided_differences(&points).unwrap();
        assert_eq!(dd, vec![r(0), r(1), r(1)]);
    }

    #[test]
    fn newton_form_expands_to_the_interpolant() {
        // The Newton form built from the divided differences must expand to the
        // same polynomial the Lagrange path produces.
        let points = [(r(0), r(2)), (r(1), r(3)), (r(3), r(11))];
        let dd = newton_divided_differences(&points).unwrap();
        let coeffs = newton_form_to_coeffs(&points, &dd).unwrap();
        let via_newton = MultiPoly::from_univariate("x", &coeffs).to_expr();
        let via_lagrange = lagrange_interpolation(&points, "x").unwrap();
        assert_certified_equal(&via_newton, &via_lagrange);
    }

    #[test]
    fn interpolation_rejects_repeated_abscissa() {
        let points = [(r(1), r(2)), (r(1), r(5))];
        assert!(newton_divided_differences(&points).is_none());
        assert!(lagrange_interpolation(&points, "x").is_none());
    }

    /// The Maclaurin coefficients of `exp` through order 4: `1/k!`.
    fn exp_series() -> Vec<Rational> {
        vec![
            r(1),
            r(1),
            Rational::new(1, 2),
            Rational::new(1, 6),
            Rational::new(1, 24),
        ]
    }

    /// Confirm that the `[m/n]` Padé's own Maclaurin series matches the input:
    /// `P − Q·A ≡ 0 (mod x^{m+n+1})`.
    fn pade_matches_series(series: &[Rational], m: usize, n: usize) -> bool {
        let (numer, denom) = pade_fraction(series, m, n).unwrap();
        let qa = poly::ratpoly_mul(&denom, series).unwrap();
        let diff = poly::ratpoly_add(&numer, &poly::ratpoly_neg(&qa).unwrap()).unwrap();
        (0..=m + n).all(|k| diff.get(k).copied().unwrap_or_else(Rational::zero).is_zero())
    }

    #[test]
    fn pade_exp_one_one() {
        // [1/1] Padé of exp = (1 + x/2) / (1 − x/2).
        let series = exp_series();
        let (numer, denom) = pade_fraction(&series, 1, 1).unwrap();
        assert_eq!(numer, vec![r(1), Rational::new(1, 2)]);
        assert_eq!(denom, vec![r(1), Rational::new(-1, 2)]);

        let got = pade(&series, 1, 1, "x").unwrap();
        let x = CasExpr::var("x");
        let expected = (CasExpr::int(1) + x.clone() * CasExpr::rat(1, 2))
            / (CasExpr::int(1) - x * CasExpr::rat(1, 2));
        assert_certified_equal(&got, &expected);
        assert!(pade_matches_series(&series, 1, 1));
    }

    #[test]
    fn pade_exp_two_two() {
        // [2/2] Padé of exp = (1 + x/2 + x²/12) / (1 − x/2 + x²/12).
        let series = exp_series();
        let (numer, denom) = pade_fraction(&series, 2, 2).unwrap();
        assert_eq!(
            numer,
            vec![r(1), Rational::new(1, 2), Rational::new(1, 12)]
        );
        assert_eq!(
            denom,
            vec![r(1), Rational::new(-1, 2), Rational::new(1, 12)]
        );

        let got = pade(&series, 2, 2, "x").unwrap();
        let x = CasExpr::var("x");
        let numer_expr = CasExpr::int(1)
            + x.clone() * CasExpr::rat(1, 2)
            + x.clone().pow(2) * CasExpr::rat(1, 12);
        let denom_expr = CasExpr::int(1) - x.clone() * CasExpr::rat(1, 2)
            + x.pow(2) * CasExpr::rat(1, 12);
        let expected = numer_expr / denom_expr;
        assert_certified_equal(&got, &expected);
        assert!(pade_matches_series(&series, 2, 2));
    }

    #[test]
    fn pade_recovers_rational_function() {
        // 1/(1−x) has Maclaurin series [1,1,1,…]; its [0/1] Padé is exactly
        // 1/(1−x).
        let series = vec![r(1); 6];
        let (numer, denom) = pade_fraction(&series, 0, 1).unwrap();
        assert_eq!(numer, vec![r(1)]);
        assert_eq!(denom, vec![r(1), r(-1)]);

        let got = pade(&series, 0, 1, "x").unwrap();
        let expected = CasExpr::int(1) / (CasExpr::int(1) - CasExpr::var("x"));
        assert_certified_equal(&got, &expected);
        assert!(pade_matches_series(&series, 0, 1));
    }

    #[test]
    fn pade_declines_when_series_too_short() {
        // A [2/2] approximant needs 5 coefficients; supplying 4 declines.
        let short = vec![r(1), r(1), Rational::new(1, 2), Rational::new(1, 6)];
        assert!(pade_fraction(&short, 2, 2).is_none());
        assert!(pade(&short, 2, 2, "x").is_none());
    }
}
