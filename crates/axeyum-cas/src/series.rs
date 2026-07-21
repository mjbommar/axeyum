//! Truncated power series (`Maclaurin`/`Taylor` polynomials about the origin).
//!
//! This module computes the `Taylor` expansion of an expression about `var = 0`,
//! truncated at a chosen degree, and returns it as an ordinary [`CasExpr`]
//! polynomial. The single public entry point is [`series`].
//!
//! Unlike the differentiation/integration kernels in the crate root, series
//! expansion is a **compute** operation, not a proof-carrying one: certifying a
//! truncated series exactly is an order-of-vanishing property that the polynomial
//! zero-test does not decide, so no certificate is attached. Correctness is
//! instead pinned down by an extensive fixture-backed test suite comparing
//! against known closed-form expansions.
//!
//! # Representation
//!
//! Internally a series is a dense, least-significant-first coefficient vector
//! ([`Series`]): index `i` holds the exact [`Rational`] coefficient of `var^i`,
//! for `i` in `0..=order`. Every arithmetic step is `checked`, so `i128` rational
//! overflow surfaces as `None` (an honest decline) rather than a panic or a wrong
//! answer.
//!
//! # Supported expressions
//!
//! - polynomials (via the canonical [`normalize`] form, then truncation);
//! - rational functions `p / q` with `q(0) != 0` (power-series division);
//! - the elementary heads `exp`, `sin`, `cos`, `atan`, `tan` of an argument that
//!   vanishes at the origin (`tan` via the `sin/cos` power-series quotient), and
//!   `ln`, `sqrt` of an argument equal to `1` at the origin (e.g. `ln(1 + a*x)`,
//!   `sqrt(1 + x)`), computed from their exact `Maclaurin` coefficients;
//! - sums, products (truncated `Cauchy` product), powers, and quotients built
//!   from the above.
//!
//! Anything else — a bare foreign variable, `abs`, an elementary head whose
//! argument does not meet the expansion-point condition, or arithmetic overflow —
//! declines to `None`.

use axeyum_ir::Rational;

use crate::{CasExpr, MultiPoly, UnaryFunc, normalize};

/// A truncated power series: a dense, least-significant-first vector of exact
/// rational coefficients. Element `i` of `coeffs` is the coefficient of `var^i`,
/// and the vector always has length `order + 1` (higher-degree terms are dropped
/// by truncation). All constructors and combinators preserve that invariant.
struct Series {
    /// Coefficients `c_0, c_1, …, c_order`, least-significant term first.
    coeffs: Vec<Rational>,
}

impl Series {
    /// The truncation order (the highest retained degree).
    fn order(&self) -> usize {
        self.coeffs.len() - 1
    }

    /// The zero series of the given truncation order.
    fn zero(order: usize) -> Series {
        Series {
            coeffs: vec![Rational::zero(); order + 1],
        }
    }

    /// The constant series `value` of the given truncation order.
    fn constant(order: usize, value: Rational) -> Series {
        let mut coeffs = vec![Rational::zero(); order + 1];
        coeffs[0] = value;
        Series { coeffs }
    }

    /// Adopt an existing coefficient vector, truncating or zero-padding it to the
    /// requested order so the length invariant holds.
    fn truncated(mut coeffs: Vec<Rational>, order: usize) -> Series {
        coeffs.truncate(order + 1);
        coeffs.resize(order + 1, Rational::zero());
        Series { coeffs }
    }

    /// Exact coefficient-wise sum of two series of equal order, or `None` on
    /// rational overflow.
    fn add(&self, other: &Series) -> Option<Series> {
        let coeffs = self
            .coeffs
            .iter()
            .zip(&other.coeffs)
            .map(|(left, right)| left.checked_add(*right))
            .collect::<Option<Vec<_>>>()?;
        Some(Series { coeffs })
    }

    /// Exact scalar multiple of the series, or `None` on rational overflow.
    fn scale(&self, factor: Rational) -> Option<Series> {
        let coeffs = self
            .coeffs
            .iter()
            .map(|coeff| coeff.checked_mul(factor))
            .collect::<Option<Vec<_>>>()?;
        Some(Series { coeffs })
    }

    /// The `Cauchy` product of two series, truncated to the shared order, or
    /// `None` on rational overflow. Coefficient `k` of the product is
    /// `sum_{i+j=k} a_i * b_j`.
    fn mul(&self, other: &Series) -> Option<Series> {
        let order = self.order();
        let mut coeffs = vec![Rational::zero(); order + 1];
        for (left_degree, left) in self.coeffs.iter().enumerate() {
            if left.is_zero() {
                continue;
            }
            for (right_degree, right) in other.coeffs.iter().enumerate() {
                let target = left_degree + right_degree;
                if target > order {
                    break;
                }
                let product = left.checked_mul(*right)?;
                coeffs[target] = coeffs[target].checked_add(product)?;
            }
        }
        Some(Series { coeffs })
    }

    /// `self` raised to a non-negative integer power, truncated to the order, or
    /// `None` on rational overflow.
    fn pow(&self, exponent: u32) -> Option<Series> {
        let mut accumulator = Series::constant(self.order(), Rational::integer(1));
        for _ in 0..exponent {
            accumulator = accumulator.mul(self)?;
        }
        Some(accumulator)
    }

    /// Power-series division `self / divisor`, truncated to the order. Requires
    /// `divisor` to have a non-zero constant term (`q(0) != 0`); otherwise, or on
    /// rational overflow, returns `None`.
    ///
    /// The quotient `c` is the unique series with `divisor * c = self` up to the
    /// truncation degree, solved by the triangular recurrence
    /// `c_k = (a_k - sum_{i=1..=k} b_i * c_{k-i}) / b_0`.
    fn div(&self, divisor: &Series) -> Option<Series> {
        let order = self.order();
        let leading = divisor.coeffs[0];
        if leading.is_zero() {
            return None;
        }
        let mut quotient = vec![Rational::zero(); order + 1];
        for degree in 0..=order {
            let mut residual = self.coeffs[degree];
            for shift in 1..=degree {
                let term = divisor.coeffs[shift].checked_mul(quotient[degree - shift])?;
                residual = residual.checked_sub(term)?;
            }
            quotient[degree] = residual.checked_div(leading)?;
        }
        Some(Series { coeffs: quotient })
    }

    /// Reconstruct the truncated series as a canonical [`CasExpr`] polynomial in
    /// `var`, using the crate's expanded sum-of-monomials form.
    fn to_expr(&self, var: &str) -> CasExpr {
        MultiPoly::from_univariate(var, &self.coeffs).to_expr()
    }
}

/// The `Taylor` polynomial of `expr` about `var = 0`, up to and including degree
/// `order`, returned as a [`CasExpr`].
///
/// Returns `None` when the expression is outside the supported fragment (a foreign
/// variable, an unsupported transcendental head, an elementary head whose argument
/// does not meet the expansion-point condition), when the expansion is undefined
/// at `0` (e.g. division by a series with zero constant term), or when exact
/// `i128` rational arithmetic overflows.
///
/// This is a **compute** function: the returned polynomial carries no certificate
/// (see the module documentation).
///
/// ```
/// use axeyum_cas::{CasExpr, equal, series, ZeroTest};
///
/// let x = CasExpr::var("x");
/// // exp(x) to order 3 = 1 + x + x²/2 + x³/6.
/// let approx = series(&x.clone().exp(), "x", 3).unwrap();
/// let expected = CasExpr::int(1)
///     + x.clone()
///     + CasExpr::rat(1, 2) * x.clone().pow(2)
///     + CasExpr::rat(1, 6) * x.pow(3);
/// assert!(matches!(equal(&approx, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn series(expr: &CasExpr, var: &str, order: usize) -> Option<CasExpr> {
    let expansion = expand_series(expr, var, order)?;
    Some(expansion.to_expr(var))
}

/// The `Taylor` polynomial of `expr` about an **arbitrary** center `var = center`,
/// up to and including degree `order`, returned in powers of `(var − center)`.
///
/// Computed by the shift identity `T_a f = (T_0 g)(var − a)` where `g(var) =
/// f(var + a)`: expand `f(var + center)` as a `Maclaurin` series (about the
/// origin), then substitute `var ↦ var − center`. The Maclaurin center (`center =
/// 0`) reduces to [`series`].
///
/// Returns `None` on the same conditions as [`series`] applied to the shifted
/// expression — in particular, a head whose shifted argument leaves the supported
/// fragment (e.g. `exp(x)` about a nonzero center needs the irrational value
/// `exp(center)` and so declines), or overflow. Polynomials, rational functions
/// with no pole at `center`, and heads like `ln`/`sqrt` whose shifted argument
/// meets the expansion condition (e.g. `ln(x)` about `1`) are supported.
///
/// ```
/// use axeyum_cas::{CasExpr, equal, series_at, ZeroTest};
///
/// let x = CasExpr::var("x");
/// // ln(x) about x = 1 to order 3: (x−1) − (x−1)²/2 + (x−1)³/3.
/// let approx = series_at(&x.clone().ln(), "x", &CasExpr::int(1), 3).unwrap();
/// let shift = x - CasExpr::int(1);
/// let expected = shift.clone() - CasExpr::rat(1, 2) * shift.clone().pow(2)
///     + CasExpr::rat(1, 3) * shift.pow(3);
/// assert!(matches!(equal(&approx, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn series_at(expr: &CasExpr, var: &str, center: &CasExpr, order: usize) -> Option<CasExpr> {
    // g(var) = f(var + center); expand about the origin.
    let shifted = expr.substitute(var, &(CasExpr::var(var) + center.clone()));
    let maclaurin = series(&shifted, var, order)?;
    // Re-express in powers of (var − center).
    Some(maclaurin.substitute(var, &(CasExpr::var(var) - center.clone())))
}

/// Compute the internal [`Series`] for `expr`. Tries the exact polynomial normal
/// form first (case 1), then falls back to the structural recurrence that also
/// covers rational and elementary heads.
fn expand_series(expr: &CasExpr, var: &str, order: usize) -> Option<Series> {
    if let Some(coeffs) = normalize(expr).and_then(|poly| poly.to_univariate(var)) {
        return Some(Series::truncated(coeffs, order));
    }
    coeffs_of(expr, var, order)
}

/// The structural series recurrence over the expression tree. Each combinator maps
/// to the corresponding truncated series operation; leaves that cannot be
/// represented with rational coefficients (a variable other than `var`) or heads
/// outside the supported set decline to `None`.
fn coeffs_of(expr: &CasExpr, var: &str, order: usize) -> Option<Series> {
    match expr {
        CasExpr::Const(value) => Some(Series::constant(order, *value)),
        CasExpr::Var(name) => {
            if name != var {
                // A foreign symbol has no rational-coefficient univariate series.
                return None;
            }
            let mut series = Series::zero(order);
            if order >= 1 {
                series.coeffs[1] = Rational::integer(1);
            }
            Some(series)
        }
        CasExpr::Add(terms) => {
            let mut accumulator = Series::zero(order);
            for term in terms {
                accumulator = accumulator.add(&coeffs_of(term, var, order)?)?;
            }
            Some(accumulator)
        }
        CasExpr::Neg(inner) => coeffs_of(inner, var, order)?.scale(Rational::integer(-1)),
        CasExpr::Mul(factors) => {
            let mut accumulator = Series::constant(order, Rational::integer(1));
            for factor in factors {
                accumulator = accumulator.mul(&coeffs_of(factor, var, order)?)?;
            }
            Some(accumulator)
        }
        CasExpr::Pow(base, exponent) => coeffs_of(base, var, order)?.pow(*exponent),
        CasExpr::Div(numerator, denominator) => {
            let top = coeffs_of(numerator, var, order)?;
            let bottom = coeffs_of(denominator, var, order)?;
            top.div(&bottom)
        }
        CasExpr::Unary(func, arg) => unary_series(*func, arg, var, order),
    }
}

/// The series of an elementary head applied to a supported argument.
///
/// The additive heads `exp`, `sin`, `cos`, `atan` require the argument to vanish
/// at the origin (`arg(0) = 0`); `ln` and `sqrt` require it to equal `1` there
/// (`arg(0) = 1`), matching `ln(1 + …)` / `sqrt(1 + …)`. Every other shape,
/// including `tan`, declines to `None`.
fn unary_series(func: UnaryFunc, arg: &CasExpr, var: &str, order: usize) -> Option<Series> {
    let argument = coeffs_of(arg, var, order)?;
    let constant_term = argument.coeffs[0];
    match func {
        UnaryFunc::Exp => require_vanishing(&argument, constant_term)
            .and_then(|inner| compose(&inner, reciprocal_factorial)),
        UnaryFunc::Sin => require_vanishing(&argument, constant_term)
            .and_then(|inner| compose(&inner, sine_coeff)),
        UnaryFunc::Cos => require_vanishing(&argument, constant_term)
            .and_then(|inner| compose(&inner, cosine_coeff)),
        UnaryFunc::Atan => require_vanishing(&argument, constant_term)
            .and_then(|inner| compose(&inner, arctangent_coeff)),
        UnaryFunc::Ln => require_unit(argument, constant_term)
            .and_then(|inner| compose(&inner, log_one_plus_coeff)),
        UnaryFunc::Sqrt => {
            require_unit(argument, constant_term).and_then(|inner| compose(&inner, binomial_half))
        }
        // tan(u) = sin(u)/cos(u); cos(u) has constant term 1 at a vanishing `u`,
        // so the power-series division is well-defined.
        UnaryFunc::Tan => {
            let inner = require_vanishing(&argument, constant_term)?;
            let sin = compose(&inner, sine_coeff)?;
            let cos = compose(&inner, cosine_coeff)?;
            sin.div(&cos)
        }
        // `abs`, `erf`, and the Si/Ci/Ei integrals are outside the
        // rational-coefficient series fragment (√π factors / logarithmic terms).
        UnaryFunc::Abs
        | UnaryFunc::Erf
        | UnaryFunc::Si
        | UnaryFunc::Ci
        | UnaryFunc::Ei
        | UnaryFunc::Li
        | UnaryFunc::Shi
        | UnaryFunc::Chi
        | UnaryFunc::FresnelS
        | UnaryFunc::FresnelC
        | UnaryFunc::BesselJ0
        | UnaryFunc::BesselJ1
        | UnaryFunc::Asin
        | UnaryFunc::Acos
        | UnaryFunc::Asinh
        | UnaryFunc::Acosh => None,
    }
}

/// For the additive heads: accept the argument only if it vanishes at the origin,
/// returning it unchanged (its constant term is already `0`).
fn require_vanishing(argument: &Series, constant_term: Rational) -> Option<Series> {
    if constant_term.is_zero() {
        Some(Series {
            coeffs: argument.coeffs.clone(),
        })
    } else {
        None
    }
}

/// For `ln` / `sqrt`: accept the argument only if it equals `1` at the origin, and
/// return the shifted inner series `arg - 1` (which then vanishes at the origin).
fn require_unit(mut argument: Series, constant_term: Rational) -> Option<Series> {
    if constant_term == Rational::integer(1) {
        argument.coeffs[0] = Rational::zero();
        Some(argument)
    } else {
        None
    }
}

/// Compose an outer analytic function, given by its `Maclaurin` coefficients
/// `outer_coeff(k)`, with an inner series that **vanishes at the origin**.
///
/// Because the inner series has valuation at least `1`, its `k`-th power has
/// valuation at least `k`, so only powers `0..=order` can contribute to the
/// truncation and the sum `sum_k outer_coeff(k) * inner^k` is finite. Returns
/// `None` on rational overflow (including a `outer_coeff` that overflows).
fn compose<F>(inner: &Series, outer_coeff: F) -> Option<Series>
where
    F: Fn(usize) -> Option<Rational>,
{
    let order = inner.order();
    let mut result = Series::zero(order);
    let mut power = Series::constant(order, Rational::integer(1));
    for degree in 0..=order {
        let weight = outer_coeff(degree)?;
        if !weight.is_zero() {
            result = result.add(&power.scale(weight)?)?;
        }
        if degree < order {
            power = power.mul(inner)?;
        }
    }
    Some(result)
}

/// `1 / degree!` as an exact rational, or `None` on `i128` overflow. Built by
/// repeated exact division so the numerator stays `1` throughout.
fn reciprocal_factorial(degree: usize) -> Option<Rational> {
    let mut result = Rational::integer(1);
    for step in 1..=degree {
        result = result.checked_div(Rational::integer(i128::try_from(step).ok()?))?;
    }
    Some(result)
}

/// Apply the alternating sign `(-1)^parity` to a magnitude: unchanged when
/// `parity` is even, negated when odd. `None` only on the (unreachable for our
/// inputs) negation overflow.
fn with_alternating_sign(parity: usize, magnitude: Rational) -> Option<Rational> {
    if parity.is_multiple_of(2) {
        Some(magnitude)
    } else {
        magnitude.checked_neg()
    }
}

/// The `Maclaurin` coefficient of `sin` at degree `k`: `0` on even degrees,
/// `(-1)^j / (2j+1)!` on odd degree `k = 2j + 1`.
fn sine_coeff(degree: usize) -> Option<Rational> {
    if degree.is_multiple_of(2) {
        return Some(Rational::zero());
    }
    with_alternating_sign((degree - 1) / 2, reciprocal_factorial(degree)?)
}

/// The `Maclaurin` coefficient of `cos` at degree `k`: `0` on odd degrees,
/// `(-1)^j / (2j)!` on even degree `k = 2j`.
fn cosine_coeff(degree: usize) -> Option<Rational> {
    if !degree.is_multiple_of(2) {
        return Some(Rational::zero());
    }
    with_alternating_sign(degree / 2, reciprocal_factorial(degree)?)
}

/// The `Maclaurin` coefficient of `atan` at degree `k`: `0` on even degrees,
/// `(-1)^j / (2j+1)` on odd degree `k = 2j + 1`.
fn arctangent_coeff(degree: usize) -> Option<Rational> {
    if degree.is_multiple_of(2) {
        return Some(Rational::zero());
    }
    let magnitude = Rational::checked_new(1, i128::try_from(degree).ok()?)?;
    with_alternating_sign((degree - 1) / 2, magnitude)
}

/// The `Maclaurin` coefficient of `ln(1 + t)` at degree `k`: `0` at `k = 0` and
/// `(-1)^{k+1} / k` for `k >= 1`.
fn log_one_plus_coeff(degree: usize) -> Option<Rational> {
    if degree == 0 {
        return Some(Rational::zero());
    }
    let magnitude = Rational::checked_new(1, i128::try_from(degree).ok()?)?;
    with_alternating_sign(degree - 1, magnitude)
}

/// The binomial coefficient `C(1/2, k)`, i.e. the `Maclaurin` coefficient of
/// `sqrt(1 + t)` at degree `k`, computed exactly as the product
/// `prod_{i=0}^{k-1} (1/2 - i) / (i + 1)`. `None` on `i128` overflow.
fn binomial_half(degree: usize) -> Option<Rational> {
    let half = Rational::new(1, 2);
    let mut result = Rational::integer(1);
    for step in 0..degree {
        let factor_numerator = half.checked_sub(Rational::integer(i128::try_from(step).ok()?))?;
        let factor_denominator = Rational::integer(i128::try_from(step + 1).ok()?);
        result = result
            .checked_mul(factor_numerator)?
            .checked_div(factor_denominator)?;
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ZeroTest, equal};

    fn var() -> CasExpr {
        CasExpr::var("x")
    }

    /// Assert two `CasExpr` polynomials are equal via the certified zero-test.
    fn assert_matches(actual: &CasExpr, expected: &CasExpr) {
        match equal(actual, expected) {
            ZeroTest::Certified { equal, witness } => {
                assert!(equal, "series mismatch; difference witness = {witness:?}");
            }
            ZeroTest::Unknown => panic!("expected a decidable (Certified) comparison"),
        }
    }

    /// The exact coefficient vector of an expansion (order + 1 entries).
    fn coeffs(expr: &CasExpr, order: usize) -> Vec<Rational> {
        expand_series(expr, "x", order)
            .expect("expansion should exist")
            .coeffs
    }

    #[test]
    fn geometric_series_one_over_one_minus_x() {
        // 1/(1-x) = 1 + x + x² + x³ + x⁴ + x⁵ (all coefficients exactly 1).
        let expr = CasExpr::int(1) / (CasExpr::int(1) - var());
        assert_eq!(coeffs(&expr, 5), vec![Rational::integer(1); 6]);

        let result = series(&expr, "x", 5).expect("rational function");
        let expected = (0..=5).fold(CasExpr::zero(), |acc, k| acc + var().pow(k));
        assert_matches(&result, &expected);
    }

    #[test]
    fn exponential_series() {
        // exp(x) = 1 + x + x²/2 + x³/6 + x⁴/24.
        let expr = var().exp();
        assert_eq!(
            coeffs(&expr, 4),
            vec![
                Rational::integer(1),
                Rational::integer(1),
                Rational::new(1, 2),
                Rational::new(1, 6),
                Rational::new(1, 24),
            ]
        );
        let result = series(&expr, "x", 4).expect("elementary");
        let expected = CasExpr::int(1)
            + var()
            + CasExpr::rat(1, 2) * var().pow(2)
            + CasExpr::rat(1, 6) * var().pow(3)
            + CasExpr::rat(1, 24) * var().pow(4);
        assert_matches(&result, &expected);
    }

    #[test]
    fn sine_series() {
        // sin(x) = x - x³/6 + x⁵/120.
        let result = series(&var().sin(), "x", 5).expect("elementary");
        let expected =
            var() - CasExpr::rat(1, 6) * var().pow(3) + CasExpr::rat(1, 120) * var().pow(5);
        assert_matches(&result, &expected);
        assert_eq!(
            coeffs(&var().sin(), 5),
            vec![
                Rational::zero(),
                Rational::integer(1),
                Rational::zero(),
                Rational::new(-1, 6),
                Rational::zero(),
                Rational::new(1, 120),
            ]
        );
    }

    #[test]
    fn cosine_series() {
        // cos(x) = 1 - x²/2 + x⁴/24.
        let result = series(&var().cos(), "x", 4).expect("elementary");
        let expected = CasExpr::int(1) - CasExpr::rat(1, 2) * var().pow(2)
            + CasExpr::rat(1, 24) * var().pow(4);
        assert_matches(&result, &expected);
    }

    #[test]
    fn logarithm_series() {
        // ln(1+x) = x - x²/2 + x³/3 - x⁴/4.
        let expr = (CasExpr::int(1) + var()).ln();
        let result = series(&expr, "x", 4).expect("elementary");
        let expected = var() - CasExpr::rat(1, 2) * var().pow(2)
            + CasExpr::rat(1, 3) * var().pow(3)
            - CasExpr::rat(1, 4) * var().pow(4);
        assert_matches(&result, &expected);
    }

    #[test]
    fn logarithm_of_one_plus_linear() {
        // ln(1 + 3x) = 3x - 9x²/2 + 9x³ - ….
        let expr = (CasExpr::int(1) + CasExpr::int(3) * var()).ln();
        assert_eq!(
            coeffs(&expr, 3),
            vec![
                Rational::zero(),
                Rational::integer(3),
                Rational::new(-9, 2),
                Rational::integer(9),
            ]
        );
    }

    #[test]
    fn arctangent_series() {
        // atan(x) = x - x³/3 + x⁵/5.
        let result = series(&var().atan(), "x", 5).expect("elementary");
        let expected =
            var() - CasExpr::rat(1, 3) * var().pow(3) + CasExpr::rat(1, 5) * var().pow(5);
        assert_matches(&result, &expected);
    }

    #[test]
    fn sqrt_one_plus_x_series() {
        // sqrt(1+x) = 1 + x/2 - x²/8 + x³/16 - ….
        let expr = (CasExpr::int(1) + var()).sqrt();
        assert_eq!(
            coeffs(&expr, 3),
            vec![
                Rational::integer(1),
                Rational::new(1, 2),
                Rational::new(-1, 8),
                Rational::new(1, 16),
            ]
        );
    }

    #[test]
    fn rational_function_one_plus_x_over_one_minus_x() {
        // (1+x)/(1-x) = 1 + 2x + 2x² + 2x³.
        let expr = (CasExpr::int(1) + var()) / (CasExpr::int(1) - var());
        let result = series(&expr, "x", 3).expect("rational function");
        let expected = CasExpr::int(1)
            + CasExpr::int(2) * var()
            + CasExpr::int(2) * var().pow(2)
            + CasExpr::int(2) * var().pow(3);
        assert_matches(&result, &expected);
        assert_eq!(
            coeffs(&expr, 3),
            vec![
                Rational::integer(1),
                Rational::integer(2),
                Rational::integer(2),
                Rational::integer(2)
            ]
        );
    }

    #[test]
    fn polynomial_truncation() {
        // (1+x)⁵ truncated at degree 3 = 1 + 5x + 10x² + 10x³.
        let expr = (CasExpr::int(1) + var()).pow(5);
        let result = series(&expr, "x", 3).expect("polynomial");
        let expected = CasExpr::int(1)
            + CasExpr::int(5) * var()
            + CasExpr::int(10) * var().pow(2)
            + CasExpr::int(10) * var().pow(3);
        assert_matches(&result, &expected);
    }

    #[test]
    fn product_of_exponentials_matches_scaled_exponential() {
        // exp(x)·exp(x) and exp(2x) must agree to any order.
        let product = var().exp() * var().exp();
        let scaled = (CasExpr::int(2) * var()).exp();
        let a = series(&product, "x", 4).expect("product");
        let b = series(&scaled, "x", 4).expect("elementary");
        assert_matches(&a, &b);
    }

    #[test]
    fn pythagorean_identity_truncates_to_one() {
        // sin²(x) + cos²(x) ≡ 1, so its series to any order is exactly 1.
        let expr = var().sin().pow(2) + var().cos().pow(2);
        let result = series(&expr, "x", 6).expect("elementary");
        assert_matches(&result, &CasExpr::one());
    }

    #[test]
    fn composition_sin_of_x_squared() {
        // sin(x²) = x² - x⁶/6 - … (inner series vanishes at the origin).
        let expr = var().pow(2).sin();
        assert_eq!(
            coeffs(&expr, 6),
            vec![
                Rational::zero(),
                Rational::zero(),
                Rational::integer(1),
                Rational::zero(),
                Rational::zero(),
                Rational::zero(),
                Rational::new(-1, 6),
            ]
        );
    }

    #[test]
    fn tangent_via_sine_over_cosine() {
        // tan x = x + x³/3 + 2x⁵/15 + … (from the power-series quotient sin/cos).
        assert_eq!(
            coeffs(&var().tan(), 5),
            vec![
                Rational::zero(),
                Rational::integer(1),
                Rational::zero(),
                Rational::new(1, 3),
                Rational::zero(),
                Rational::new(2, 15),
            ]
        );
        // tan(2x) = 2x + 8x³/3 + … (linear-argument scaling).
        assert_eq!(
            coeffs(&(CasExpr::int(2) * var()).tan(), 3),
            vec![
                Rational::zero(),
                Rational::integer(2),
                Rational::zero(),
                Rational::new(8, 3),
            ]
        );
    }

    #[test]
    fn unsupported_foreign_variable_returns_none() {
        // exp(y) has no rational univariate series in x.
        assert!(series(&CasExpr::var("y").exp(), "x", 4).is_none());
        // A polynomial with a symbolic (non-x) coefficient is likewise unsupported.
        assert!(series(&(var().pow(2) + CasExpr::var("c")), "x", 4).is_none());
    }

    #[test]
    fn sqrt_of_bare_variable_returns_none() {
        // sqrt(x) is singular at 0 (argument does not equal 1 there): honest None.
        assert!(series(&var().sqrt(), "x", 4).is_none());
    }

    #[test]
    fn division_by_zero_constant_term_returns_none() {
        // 1/x has no Maclaurin series (denominator vanishes at 0).
        assert!(series(&(CasExpr::int(1) / var()), "x", 4).is_none());
    }
}
