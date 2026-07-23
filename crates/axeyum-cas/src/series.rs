//! Truncated power series (`Maclaurin`/`Taylor` polynomials about the origin).
//!
//! This module computes the `Taylor` expansion of an expression about `var = 0`
//! ([`series`]) or an arbitrary center ([`series_at`]), truncated at a chosen
//! degree, and returns it as an ordinary [`CasExpr`] polynomial. Expansion about a
//! nonzero center whose coefficients leave the rational fragment (e.g. `exp(x)`
//! about `x = 1`, coefficients `e/n!`) falls back to the derivative definition
//! `cₙ = f⁽ⁿ⁾(center)/n!`, which admits arbitrary closed-form constants.
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
//! - integer-order cylindrical and modified Bessel functions `J_n` and `I_n` of
//!   an argument that vanishes at the origin;
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

/// The Laurent expansion at the origin of a ratio `N(x)/D(x)` with a pole there —
/// `D` vanishes to order `m`, `N` to order `k < m`, giving a principal part of order
/// `p = m − k`. Cancels the common `xᵏ`, divides the two regular series, and shifts
/// the (regular) quotient down by `p` to emit the negative-power terms. Covers
/// transcendental poles like `1/sin x`, `1/(eˣ−1)`, `cot x = cos x/sin x`. Returns
/// `None` when `expr` is not a division or the ratio is regular (handled elsewhere).
fn laurent_ratio_at_origin(expr: &CasExpr, var: &str, order: usize) -> Option<CasExpr> {
    let CasExpr::Div(numerator, denominator) = expr else {
        return None;
    };
    // Denominator valuation `m` (lowest order with a nonzero coefficient).
    let den_probe = coeffs_of(denominator, var, order.saturating_add(2))?;
    let m = den_probe.coeffs.iter().position(|c| !c.is_zero())?;
    if m == 0 {
        return None; // no pole from the denominator — regular case
    }
    let num_probe = coeffs_of(numerator, var, order.saturating_add(2))?;
    let k = num_probe
        .coeffs
        .iter()
        .position(|c| !c.is_zero())
        .unwrap_or(usize::MAX);
    if k >= m {
        return None; // removable / regular — handled by the normal series path
    }
    let pole = m - k; // order of the pole
    // Need the regular quotient to order `order + pole` so that after the `x^{−pole}`
    // shift the expansion runs from `x^{−pole}` up to `x^{order}`.
    let target = order.checked_add(pole)?;
    let top = coeffs_of(numerator, var, target.checked_add(k)?)?;
    let bottom = coeffs_of(denominator, var, target.checked_add(m)?)?;
    let top_shifted = Series::truncated(top.coeffs[k..].to_vec(), target);
    let bottom_shifted = Series::truncated(bottom.coeffs[m..].to_vec(), target);
    let quotient = top_shifted.div(&bottom_shifted)?;
    // Emit `Σ_j q_j · x^{j − pole}` (negative exponents as `1/xⁿ`).
    let pole_i = i64::try_from(pole).ok()?;
    let mut terms: Vec<CasExpr> = Vec::new();
    for (j, coefficient) in quotient.coeffs.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let exponent = i64::try_from(j).ok()? - pole_i;
        terms.push(build_power_term(*coefficient, var, exponent)?);
    }
    match terms.len() {
        0 => Some(CasExpr::zero()),
        1 => terms.pop(),
        _ => Some(CasExpr::Add(terms)),
    }
}

/// `coefficient · varᵉ` for a possibly-negative integer exponent `e` (negative
/// exponents rendered as `coefficient / var^{|e|}`).
fn build_power_term(coefficient: Rational, var: &str, exponent: i64) -> Option<CasExpr> {
    let coeff = CasExpr::Const(coefficient);
    match exponent {
        0 => Some(coeff),
        e if e > 0 => Some(coeff * CasExpr::var(var).pow(u32::try_from(e).ok()?)),
        e => Some(coeff / CasExpr::var(var).pow(u32::try_from(-e).ok()?)),
    }
}

/// The **root degree** `q` of the first `root_q(var)` / `√var` subexpression whose
/// argument is exactly `var` — the fractional-power denominator a Puiseux expansion
/// substitutes on. `None` if there is no such root of the bare variable.
fn root_degree_of(expr: &CasExpr, var: &str) -> Option<u32> {
    match expr {
        CasExpr::Unary(UnaryFunc::Sqrt, arg) if matches!(arg.as_ref(), CasExpr::Var(v) if v == var) => {
            Some(2)
        }
        CasExpr::Unary(UnaryFunc::NthRoot(q), arg)
            if matches!(arg.as_ref(), CasExpr::Var(v) if v == var) =>
        {
            Some(*q)
        }
        CasExpr::Unary(_, a) | CasExpr::Neg(a) | CasExpr::Pow(a, _) => root_degree_of(a, var),
        CasExpr::Div(a, b) => root_degree_of(a, var).or_else(|| root_degree_of(b, var)),
        CasExpr::Add(items) | CasExpr::Mul(items) => items.iter().find_map(|t| root_degree_of(t, var)),
        CasExpr::Const(_) | CasExpr::Var(_) => None,
    }
}

/// The **Puiseux expansion** at the origin of a function of a single root `x^{1/q}`:
/// substitute `t = x^{1/q}` (`root_q(x) → t`, `x → tᵠ`), take the ordinary Taylor
/// series in `t` to order `q·order`, then re-substitute `t → x^{1/q}`. So
/// `sin√x = √x − x√x/6 + …`, `e^{∛x} = 1 + ∛x + ∛x²/2 + …`. `None` unless a single
/// root degree governs the expansion.
fn puiseux_at_origin(expr: &CasExpr, var: &str, order: usize) -> Option<CasExpr> {
    // Operate on the un-shifted `expr` (center is 0) so the root heads are not
    // atomized (`simplify(exp(√x))` collapses to an opaque atom).
    let q = root_degree_of(expr, var)?;
    let t = if var == "t" { "s" } else { "t" };
    let root = if q == 2 {
        CasExpr::var(var).sqrt()
    } else {
        CasExpr::Unary(UnaryFunc::NthRoot(q), Box::new(CasExpr::var(var)))
    };
    // `root_q(x) → t`, then remaining `x → tᵠ`.
    let in_t = crate::replace_subexpr(expr, &root, &CasExpr::var(t))
        .substitute(var, &CasExpr::var(t).pow(q));
    // Need `q·order` Taylor terms in `t` to recover `order` in `x`.
    let taylor = series_at(&in_t, t, &CasExpr::int(0), order.checked_mul(q as usize)?)?;
    Some(crate::simplify(&taylor.substitute(t, &root)))
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
    if let Some(maclaurin) = series(&shifted, var, order) {
        // Re-express in powers of (var − center).
        return Some(maclaurin.substitute(var, &(CasExpr::var(var) - center.clone())));
    }
    // Laurent fallback: a ratio `N/D` with a pole at the center (`D` vanishes to a
    // higher order than `N`) has a principal part of negative powers — `1/sin x =
    // 1/x + x/6 + …`, `1/(eˣ−1) = 1/x − 1/2 + x/12 − …`, `cot x`, `csc x`.
    if let Some(laurent) = laurent_ratio_at_origin(&shifted, var, order) {
        return Some(laurent.substitute(var, &(CasExpr::var(var) - center.clone())));
    }
    // Puiseux fallback (center 0 only): a function of a root `x^{1/q}` — substitute
    // `t = x^{1/q}`, Taylor-expand in `t`, then re-substitute — `sin√x = √x − x√x/6 + …`.
    if matches!(center, CasExpr::Const(c) if c.is_zero())
        && let Some(puiseux) = puiseux_at_origin(expr, var, order)
    {
        return Some(puiseux);
    }
    // The rational-coefficient series ring declined — commonly because a head's
    // shifted argument needs a transcendental value at the center (e.g. `exp(x)`
    // about `x = 1` has coefficients `e/n!`). Fall back to the Taylor definition
    // `cₙ = f⁽ⁿ⁾(center)/n!`, whose coefficients are arbitrary closed-form
    // constants rather than rationals.
    taylor_by_derivatives(expr, var, center, order)
}

/// `Taylor` polynomial by the derivative definition: `Σ_{n=0}^{order}
/// f⁽ⁿ⁾(center)/n! · (var − center)ⁿ`. Unlike the series-ring recurrence this
/// admits transcendental coefficients (`e`, `sin(1)`, …), so it covers centers
/// where a head leaves the rational fragment.
///
/// Declines (`None`) when a coefficient fails to reduce to a finite constant —
/// either it still mentions `var` (a head we cannot differentiate to closed form)
/// or it is non-finite (a pole at the center, e.g. a rational function whose
/// denominator vanishes there).
fn taylor_by_derivatives(
    expr: &CasExpr,
    var: &str,
    center: &CasExpr,
    order: usize,
) -> Option<CasExpr> {
    let shift = CasExpr::var(var) - center.clone();
    let mut terms: Vec<CasExpr> = Vec::with_capacity(order + 1);
    let mut factorial = Rational::integer(1);
    for n in 0..=order {
        if n >= 1 {
            factorial = factorial * Rational::integer(i128::try_from(n).ok()?);
        }
        let derivative = expr.differentiate_n(var, n);
        let coefficient = crate::fold_elementary_constants(&crate::simplify(
            &derivative.substitute(var, center),
        ));
        // A genuine constant coefficient: no residual `var`, and finite (no pole).
        if crate::expr_contains_var(&coefficient, var) {
            return None;
        }
        if !crate::evalf(&coefficient, &[]).is_some_and(f64::is_finite) {
            return None;
        }
        if matches!(&coefficient, CasExpr::Const(c) if c.is_zero()) {
            continue;
        }
        let scaled = crate::simplify(
            &(coefficient * CasExpr::Const(Rational::integer(1).checked_div(factorial)?)),
        );
        let term = match n {
            0 => scaled,
            1 => scaled * shift.clone(),
            _ => scaled * shift.clone().pow(u32::try_from(n).ok()?),
        };
        terms.push(term);
    }
    if terms.is_empty() {
        return Some(CasExpr::zero());
    }
    // Return in powers of `(var − center)` (matching the rational-series path);
    // a full `simplify` here would distribute those powers back into powers of
    // `var`.
    Some(CasExpr::Add(terms))
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
            let bottom = coeffs_of(denominator, var, order)?;
            // Lowest order at which the denominator is nonzero.
            let m = bottom.coeffs.iter().position(|c| !c.is_zero())?;
            if m == 0 {
                let top = coeffs_of(numerator, var, order)?;
                return top.div(&bottom);
            }
            // Removable singularity: `D = xᵐ·d(x)` with `d(0) ≠ 0`. Compute `order+m`
            // coefficients so that after cancelling the common `xᵐ` factor from
            // numerator and denominator, `order+1` terms of the quotient remain — e.g.
            // `x/(eˣ−1) = 1 − x/2 + x²/12 − …` (the Bernoulli generating function).
            let top = coeffs_of(numerator, var, order + m)?;
            let bottom = coeffs_of(denominator, var, order + m)?;
            // The numerator must vanish to at least order `m`, else it is a true pole
            // (out of the Taylor fragment — a Laurent expansion would be needed).
            if top.coeffs.iter().take(m).any(|c| !c.is_zero()) {
                return None;
            }
            let top_shifted = Series { coeffs: top.coeffs[m..].to_vec() };
            let bottom_shifted = Series { coeffs: bottom.coeffs[m..].to_vec() };
            top_shifted.div(&bottom_shifted)
        }
        CasExpr::Unary(func, arg) => unary_series(*func, arg, var, order),
    }
}

/// The series of an elementary head applied to a supported argument.
///
/// The additive heads `exp`, `sin`, `cos`, `atan`, `J_n`, and `I_n` require the
/// argument to vanish at the origin (`arg(0) = 0`); `ln` and `sqrt` require it to
/// equal `1` there (`arg(0) = 1`), matching `ln(1 + …)` / `sqrt(1 + …)`.
/// Every other shape declines to `None`.
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
        UnaryFunc::Asin => require_vanishing(&argument, constant_term)
            .and_then(|inner| compose(&inner, arcsine_coeff)),
        UnaryFunc::Asinh => require_vanishing(&argument, constant_term)
            .and_then(|inner| compose(&inner, arcsinh_coeff)),
        UnaryFunc::BesselJ(n) => require_vanishing(&argument, constant_term)
            .and_then(|inner| compose(&inner, |degree| bessel_coeff(n, false, degree))),
        UnaryFunc::BesselI(n) => require_vanishing(&argument, constant_term)
            .and_then(|inner| compose(&inner, |degree| bessel_coeff(n, true, degree))),
        UnaryFunc::Ln => require_unit(argument, constant_term)
            .and_then(|inner| compose(&inner, log_one_plus_coeff)),
        UnaryFunc::Sqrt => {
            require_unit(argument, constant_term).and_then(|inner| compose(&inner, binomial_half))
        }
        // `root_q(1+u) = (1+u)^{1/q} = Σ C(1/q, d) uᵈ` — the fractional binomial series
        // (the `q`-th-root generalization of `√` / `binomial_half`).
        UnaryFunc::NthRoot(q) => require_unit(argument, constant_term)
            .and_then(|inner| compose(&inner, |degree| binomial_reciprocal(q, degree))),
        // tan(u) = sin(u)/cos(u); cos(u) has constant term 1 at a vanishing `u`,
        // so the power-series division is well-defined.
        UnaryFunc::Tan => {
            let inner = require_vanishing(&argument, constant_term)?;
            let sin = compose(&inner, sine_coeff)?;
            let cos = compose(&inner, cosine_coeff)?;
            sin.div(&cos)
        }
        // `abs`, `sign`/`floor`/`ceiling` (not analytic at integers / the origin),
        // `erf`, and the Si/Ci/Ei integrals are outside the rational-coefficient
        // series fragment (√π factors / logarithmic terms).
        UnaryFunc::Abs
        | UnaryFunc::Sign
        | UnaryFunc::Floor
        | UnaryFunc::Ceiling
        | UnaryFunc::Erf
        | UnaryFunc::Si
        | UnaryFunc::Ci
        | UnaryFunc::Ei
        | UnaryFunc::Li
        | UnaryFunc::Shi
        | UnaryFunc::Chi
        | UnaryFunc::FresnelS
        | UnaryFunc::FresnelC
        // acos = π/2 − asin has an irrational (π/2) constant term; acosh is
        // undefined at 0 (|x|<1) — neither has a rational Maclaurin series.
        | UnaryFunc::Acos
        | UnaryFunc::Acosh
        | UnaryFunc::Gamma
        | UnaryFunc::PolyGamma(_)
        | UnaryFunc::Ai
        | UnaryFunc::AiPrime
        | UnaryFunc::Bi
        | UnaryFunc::BiPrime
        | UnaryFunc::LambertW => None,
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

/// The degree-`d` `Maclaurin` coefficient of the non-negative integer-order
/// Bessel functions `J_n` and `I_n`:
///
/// `J_n(x) = Σ_k (-1)^k (x/2)^(n+2k) / (k! (n+k)!)`,
/// `I_n(x) = Σ_k        (x/2)^(n+2k) / (k! (n+k)!)`.
///
/// The nonzero coefficients are built from the checked recurrence
/// `c_0 = 1 / (2^n n!)` and `c_k = c_(k-1) / (4k(n+k))`; `J_n` additionally
/// alternates the sign. The valuation check happens before either loop, so an
/// order larger than the requested degree returns exact zero in constant time.
fn bessel_coeff(order: u32, modified: bool, degree: usize) -> Option<Rational> {
    let order = usize::try_from(order).ok()?;
    if degree < order || !(degree - order).is_multiple_of(2) {
        return Some(Rational::zero());
    }

    let mut magnitude = Rational::integer(1);
    for step in 1..=order {
        let divisor = i128::try_from(step).ok()?.checked_mul(2)?;
        magnitude = magnitude.checked_div(Rational::integer(divisor))?;
    }

    let radial_degree = (degree - order) / 2;
    for step in 1..=radial_degree {
        let order_plus_step = order.checked_add(step)?;
        let divisor = i128::try_from(step)
            .ok()?
            .checked_mul(i128::try_from(order_plus_step).ok()?)?
            .checked_mul(4)?;
        magnitude = magnitude.checked_div(Rational::integer(divisor))?;
    }

    if modified {
        Some(magnitude)
    } else {
        with_alternating_sign(radial_degree, magnitude)
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

/// The `Maclaurin` coefficient of `asin(t)` at degree `k`: `0` at even `k`, and
/// `C(2n,n)/(4ⁿ(2n+1))` at `k = 2n+1` — computed exactly as
/// `[∏_{i=1}^{n} (2i−1)/(2i)] / (2n+1)`. `None` on `i128` overflow.
fn arcsine_coeff(degree: usize) -> Option<Rational> {
    if degree.is_multiple_of(2) {
        return Some(Rational::zero());
    }
    let n = (degree - 1) / 2;
    let mut product = Rational::integer(1);
    for i in 1..=n {
        let num = Rational::integer(i128::try_from(2 * i - 1).ok()?);
        let den = Rational::integer(i128::try_from(2 * i).ok()?);
        product = product.checked_mul(num)?.checked_div(den)?;
    }
    product.checked_div(Rational::integer(i128::try_from(degree).ok()?))
}

/// The `Maclaurin` coefficient of `asinh(t)` at degree `k`: `(−1)ⁿ` times the
/// `asin` coefficient at `k = 2n+1` (`0` at even `k`).
fn arcsinh_coeff(degree: usize) -> Option<Rational> {
    if degree.is_multiple_of(2) {
        return Some(Rational::zero());
    }
    with_alternating_sign((degree - 1) / 2, arcsine_coeff(degree)?)
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
/// Coefficient of `uᵈ` in `(1+u)^{1/q} = Σ_d C(1/q, d) uᵈ` — the fractional binomial
/// series for the `q`-th root, generalizing [`binomial_half`] (the `q = 2` case).
fn binomial_reciprocal(q: u32, degree: usize) -> Option<Rational> {
    let exponent = Rational::checked_new(1, i128::from(q))?;
    let mut result = Rational::integer(1);
    for step in 0..degree {
        let factor_numerator = exponent.checked_sub(Rational::integer(i128::try_from(step).ok()?))?;
        let factor_denominator = Rational::integer(i128::try_from(step + 1).ok()?);
        result = result
            .checked_mul(factor_numerator)?
            .checked_div(factor_denominator)?;
    }
    Some(result)
}

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
    fn puiseux_series() {
        use crate::{CasExpr as C, evalf, series_at};
        let at0 = |e: &C, n| series_at(e, "x", &C::int(0), n).expect("Puiseux");
        // sin√x = √x − (√x)³/6 + (√x)⁵/120.
        let s = at0(&var().sqrt().sin(), 3);
        let s_expected = var().sqrt() - C::rat(1, 6) * var().sqrt().pow(3) + C::rat(1, 120) * var().sqrt().pow(5);
        assert_matches(&s, &s_expected);
        // e^√x = 1 + √x + (√x)²/2 + (√x)³/6 + (√x)⁴/24 (mixed integer/half-integer).
        let e = at0(&var().sqrt().exp(), 2);
        assert!((evalf(&e, &[("x", 0.25)]).unwrap() - 0.25_f64.sqrt().exp()).abs() < 1e-3);
        // Cube-root Puiseux e^∛x, verified numerically.
        let c = at0(&var().cbrt().exp(), 2);
        assert!((evalf(&c, &[("x", 0.064)]).unwrap() - 0.064_f64.cbrt().exp()).abs() < 1e-3);
    }

    #[test]
    fn transcendental_laurent_series() {
        use crate::{CasExpr as C, series_at};
        let at0 = |e: &C, n| series_at(e, "x", &C::int(0), n).expect("Laurent");
        // 1/sin x = 1/x + x/6 + 7x³/360 (odd principal part + Taylor tail).
        let csc = at0(&(C::int(1) / var().sin()), 4);
        let csc_expected = C::int(1) / var()
            + C::rat(1, 6) * var()
            + C::rat(7, 360) * var().pow(3);
        assert_matches(&csc, &csc_expected);
        // 1/(eˣ−1) = 1/x − 1/2 + x/12 − x³/720 (Bernoulli, pole form).
        let bose = at0(&(C::int(1) / (var().exp() - C::int(1))), 3);
        let bose_expected = C::int(1) / var() - C::rat(1, 2) + C::rat(1, 12) * var()
            - C::rat(1, 720) * var().pow(3);
        assert_matches(&bose, &bose_expected);
        // cot x = cos x/sin x = 1/x − x/3 − x³/45.
        let cot = at0(&(var().cos() / var().sin()), 4);
        let cot_expected = C::int(1) / var() - C::rat(1, 3) * var() - C::rat(1, 45) * var().pow(3);
        assert_matches(&cot, &cot_expected);
        // Double pole: 1/(x·sin x) = 1/x² + 1/6 + 7x²/360.
        let double = at0(&(C::int(1) / (var() * var().sin())), 2);
        let double_expected = C::int(1) / var().pow(2) + C::rat(1, 6) + C::rat(7, 360) * var().pow(2);
        assert_matches(&double, &double_expected);
    }

    #[test]
    fn removable_singularity_ratio_series() {
        use crate::CasExpr as C;
        // x/(eˣ−1) = 1 − x/2 + x²/12 − x⁴/720 (Bernoulli generating function): both
        // numerator and denominator vanish at 0, but the ratio is regular.
        let bernoulli = var() / (var().exp() - C::int(1));
        assert_eq!(
            coeffs(&bernoulli, 4),
            vec![
                Rational::integer(1),
                Rational::new(-1, 2),
                Rational::new(1, 12),
                Rational::zero(),
                Rational::new(-1, 720),
            ]
        );
        // sin(x)/x = 1 − x²/6 + x⁴/120; (1−cos x)/x² = 1/2 − x²/24.
        assert_eq!(
            coeffs(&(var().sin() / var()), 4),
            vec![Rational::integer(1), Rational::zero(), Rational::new(-1, 6), Rational::zero(), Rational::new(1, 120)]
        );
        assert_eq!(
            coeffs(&((C::int(1) - var().cos()) / var().pow(2)), 2),
            vec![Rational::new(1, 2), Rational::zero(), Rational::new(-1, 24)]
        );
        // A genuine pole (numerator does not vanish) declines — Taylor can't reach it.
        assert!(series(&(C::int(1) / var()), "x", 4).is_none());
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
    fn arcsine_arcsinh_series() {
        // asin(x) = x + x³/6 + 3x⁵/40 (even coefficients zero).
        let asin = CasExpr::Unary(UnaryFunc::Asin, Box::new(var()));
        assert_eq!(
            coeffs(&asin, 5),
            vec![
                Rational::zero(),
                Rational::integer(1),
                Rational::zero(),
                Rational::new(1, 6),
                Rational::zero(),
                Rational::new(3, 40),
            ]
        );
        // asinh(x) = x − x³/6 + 3x⁵/40 (alternating).
        let asinh = CasExpr::Unary(UnaryFunc::Asinh, Box::new(var()));
        assert_eq!(
            coeffs(&asinh, 5),
            vec![
                Rational::zero(),
                Rational::integer(1),
                Rational::zero(),
                Rational::new(-1, 6),
                Rational::zero(),
                Rational::new(3, 40),
            ]
        );
        // acos (π/2 constant) and acosh (undefined at 0) have no rational series.
        assert!(series(&CasExpr::Unary(UnaryFunc::Acos, Box::new(var())), "x", 4).is_none());
        assert!(series(&CasExpr::Unary(UnaryFunc::Acosh, Box::new(var())), "x", 4).is_none());
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
    fn taylor_about_center_with_transcendental_coefficients() {
        use crate::series_at;
        // exp(x) about x=1: e·[1 + (x−1) + (x−1)²/2 + (x−1)³/6]. The rational
        // series ring cannot hold the coefficient `e`; the derivative fallback can.
        let e = CasExpr::int(1).exp();
        let s = || var() - CasExpr::int(1);
        let got = series_at(&var().exp(), "x", &CasExpr::int(1), 3).expect("taylor fallback");
        let expected = e.clone()
            + e.clone() * s()
            + e.clone() * CasExpr::rat(1, 2) * s().pow(2)
            + e * CasExpr::rat(1, 6) * s().pow(3);
        assert!(matches!(equal(&got, &expected), ZeroTest::Certified { equal: true, .. }));

        // sin(x) about x=π/6, order 1: 1/2 + (√3/2)(x − π/6).
        let center = crate::CasExpr::var("pi") / CasExpr::int(6);
        let got = series_at(&var().sin(), "x", &center, 1).expect("taylor fallback");
        let expected = CasExpr::rat(1, 2)
            + CasExpr::rat(1, 2) * CasExpr::int(3).sqrt() * (var() - center);
        assert!(matches!(equal(&got, &expected), ZeroTest::Certified { equal: true, .. }));

        // A simple pole at the center now expands as its Laurent series: 1/x → 1/x.
        let pole = series_at(&(CasExpr::int(1) / var()), "x", &CasExpr::int(0), 2).expect("Laurent");
        assert!(matches!(equal(&pole, &(CasExpr::int(1) / var())), ZeroTest::Certified { equal: true, .. }));
        // A branch point (ln x about 0) has no Laurent series — still declines.
        assert!(series_at(&var().ln(), "x", &CasExpr::int(0), 2).is_none());
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
    fn integer_order_bessel_maclaurin_fixtures() {
        // DLMF 10.2.E2 / 10.25.E2, independently cross-checked against SymPy.
        assert_eq!(
            coeffs(&var().bessel_j(0), 8),
            vec![
                Rational::integer(1),
                Rational::zero(),
                Rational::new(-1, 4),
                Rational::zero(),
                Rational::new(1, 64),
                Rational::zero(),
                Rational::new(-1, 2_304),
                Rational::zero(),
                Rational::new(1, 147_456),
            ]
        );
        assert_eq!(
            coeffs(&var().bessel_j(1), 9),
            vec![
                Rational::zero(),
                Rational::new(1, 2),
                Rational::zero(),
                Rational::new(-1, 16),
                Rational::zero(),
                Rational::new(1, 384),
                Rational::zero(),
                Rational::new(-1, 18_432),
                Rational::zero(),
                Rational::new(1, 1_474_560),
            ]
        );
        assert_eq!(
            coeffs(&var().bessel_j(2), 8),
            vec![
                Rational::zero(),
                Rational::zero(),
                Rational::new(1, 8),
                Rational::zero(),
                Rational::new(-1, 96),
                Rational::zero(),
                Rational::new(1, 3_072),
                Rational::zero(),
                Rational::new(-1, 184_320),
            ]
        );
        assert_eq!(
            coeffs(&var().bessel_i(0), 8),
            vec![
                Rational::integer(1),
                Rational::zero(),
                Rational::new(1, 4),
                Rational::zero(),
                Rational::new(1, 64),
                Rational::zero(),
                Rational::new(1, 2_304),
                Rational::zero(),
                Rational::new(1, 147_456),
            ]
        );
        assert_eq!(
            coeffs(&var().bessel_i(1), 9),
            vec![
                Rational::zero(),
                Rational::new(1, 2),
                Rational::zero(),
                Rational::new(1, 16),
                Rational::zero(),
                Rational::new(1, 384),
                Rational::zero(),
                Rational::new(1, 18_432),
                Rational::zero(),
                Rational::new(1, 1_474_560),
            ]
        );
        assert_eq!(
            coeffs(&var().bessel_i(2), 8),
            vec![
                Rational::zero(),
                Rational::zero(),
                Rational::new(1, 8),
                Rational::zero(),
                Rational::new(1, 96),
                Rational::zero(),
                Rational::new(1, 3_072),
                Rational::zero(),
                Rational::new(1, 184_320),
            ]
        );
    }

    #[test]
    fn bessel_series_composition_and_differential_equations() {
        // Composition must retain inner scaling and nonlinear terms exactly.
        assert_eq!(
            coeffs(&(CasExpr::int(2) * var()).bessel_j(0), 8),
            vec![
                Rational::integer(1),
                Rational::zero(),
                Rational::integer(-1),
                Rational::zero(),
                Rational::new(1, 4),
                Rational::zero(),
                Rational::new(-1, 36),
                Rational::zero(),
                Rational::new(1, 576),
            ]
        );
        assert_eq!(
            coeffs(&(var() + var().pow(2)).bessel_i(1), 6),
            vec![
                Rational::zero(),
                Rational::new(1, 2),
                Rational::new(1, 2),
                Rational::new(1, 16),
                Rational::new(3, 16),
                Rational::new(73, 384),
                Rational::new(29, 384),
            ]
        );

        // Independently check every computed coefficient against the defining ODEs:
        // x²y'' + xy' + (x²−n²)y = 0 for J_n and
        // x²y'' + xy' − (x²+n²)y = 0 for I_n.
        for modified in [false, true] {
            for order in 0_u32..=16 {
                let expr = if modified {
                    var().bessel_i(order)
                } else {
                    var().bessel_j(order)
                };
                let coefficients = coeffs(&expr, 24);
                let order = i128::from(order);
                for degree in 0..=24 {
                    let degree_i128 = i128::try_from(degree).expect("small fixture degree");
                    let factor = degree_i128 * degree_i128 - order * order;
                    let current = coefficients[degree]
                        .checked_mul(Rational::integer(factor))
                        .expect("small exact ODE coefficient");
                    let prior = degree
                        .checked_sub(2)
                        .map_or(Rational::zero(), |index| coefficients[index]);
                    let expected = if modified {
                        prior
                    } else {
                        prior.checked_neg().expect("small exact ODE coefficient")
                    };
                    assert_eq!(
                        current, expected,
                        "Bessel ODE mismatch: modified={modified}, order={order}, degree={degree}"
                    );
                }
            }
        }
    }

    #[test]
    fn bessel_series_limits_and_checked_boundaries() {
        use crate::{LimitPoint, limit};

        // J_n(x)/x^n and I_n(x)/x^n both approach 1/(2^n n!) at zero.
        for order in 0_u32..=8 {
            let denominator = var().pow(order);
            let expected = CasExpr::Const(
                bessel_coeff(order, false, usize::try_from(order).expect("small order"))
                    .expect("small exact leading coefficient"),
            );
            for numerator in [var().bessel_j(order), var().bessel_i(order)] {
                let actual = limit(
                    &(numerator / denominator.clone()),
                    "x",
                    LimitPoint::Finite(Rational::zero()),
                )
                .expect("removable Bessel limit");
                assert_matches(&actual, &expected);
            }
        }

        // The first unrepresentable exact coefficient declines instead of wrapping.
        assert!(series(&var().bessel_j(0), "x", 32).is_some());
        assert!(series(&var().bessel_j(0), "x", 34).is_none());
        assert!(series(&var().bessel_i(0), "x", 32).is_some());
        assert!(series(&var().bessel_i(0), "x", 34).is_none());
        assert!(series(&var().bessel_j(1), "x", 33).is_some());
        assert!(series(&var().bessel_j(1), "x", 35).is_none());

        // Orders beyond the requested truncation are identically zero to that degree
        // and must not trigger an order-sized loop.
        let huge_j = series(&var().bessel_j(u32::MAX), "x", 8).expect("zero truncation");
        let huge_i = series(&var().bessel_i(u32::MAX), "x", 8).expect("zero truncation");
        assert_matches(&huge_j, &CasExpr::zero());
        assert_matches(&huge_i, &CasExpr::zero());

        // This rational Maclaurin path intentionally requires a vanishing argument.
        assert!(series(&(CasExpr::int(1) + var()).bessel_j(0), "x", 8).is_none());
        assert!(series(&CasExpr::var("y").bessel_i(1), "x", 8).is_none());
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
    fn nth_root_binomial_series() {
        // (1+x)^{1/3} = 1 + x/3 − x²/9 + 5x³/81 − … (fractional binomial series).
        let cube = CasExpr::Unary(UnaryFunc::NthRoot(3), Box::new(CasExpr::int(1) + var()));
        assert_eq!(
            coeffs(&cube, 3),
            vec![
                Rational::integer(1),
                Rational::new(1, 3),
                Rational::new(-1, 9),
                Rational::new(5, 81),
            ]
        );
        // (1−x)^{1/4} = 1 − x/4 − 3x²/32 − … (composes with the inner series `1−x`).
        let quartic = CasExpr::Unary(UnaryFunc::NthRoot(4), Box::new(CasExpr::int(1) - var()));
        assert_eq!(
            coeffs(&quartic, 2),
            vec![Rational::integer(1), Rational::new(-1, 4), Rational::new(-3, 32)]
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
