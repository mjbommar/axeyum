//! `axeyum.cas` — special values, hyperbolic heads, orthogonal polynomials and
//! rational approximation (tier R).
//!
//! The special-value functions are **exact**: `gamma(Fraction(1, 2))` is the
//! symbolic `sqrt(pi)`-shaped expression the CAS represents, not a float, and a
//! value outside the closed-form fragment is `None`. Nothing here evaluates
//! numerically — `cas.evalf` is the function that does.

use pyo3::prelude::*;

use crate::stub_types::PyFraction;
use pyo3::types::{PyAny, PyModule};

use crate::cas::expr::Expr;
use crate::cas::ntheory::rational_arg;
use crate::cas::rational;

/// Binds `fn(&CasExpr) -> CasExpr` from `hyperbolic`.
macro_rules! hyperbolic {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a total builder — it always returns an expression.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $name(expr: &Expr) -> Expr {
            Expr::wrap(axeyum_cas::hyperbolic::$name(expr.inner()))
        }
    };
}

hyperbolic!(sinh, "The hyperbolic sine, as an exponential expression.");
hyperbolic!(cosh, "The hyperbolic cosine.");
hyperbolic!(tanh, "The hyperbolic tangent.");
hyperbolic!(coth, "The hyperbolic cotangent.");
hyperbolic!(sech, "The hyperbolic secant.");
hyperbolic!(csch, "The hyperbolic cosecant.");
hyperbolic!(asinh, "The inverse hyperbolic sine, as a logarithm.");
hyperbolic!(acosh, "The inverse hyperbolic cosine.");
hyperbolic!(atanh, "The inverse hyperbolic tangent.");

/// Binds `fn(u32, &str) -> Option<CasExpr>` from `orthopoly`.
macro_rules! orthogonal {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a pure function of `n` and the variable name. `None` is
        /// `i128` coefficient overflow at large `n`.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $name(n: u32, var: &str) -> Option<Expr> {
            Expr::wrap_option(axeyum_cas::orthopoly::$name(n, var))
        }
    };
}

orthogonal!(chebyshev_t, "The Chebyshev polynomial of the first kind.");
orthogonal!(chebyshev_u, "The Chebyshev polynomial of the second kind.");
orthogonal!(legendre, "The Legendre polynomial.");
orthogonal!(hermite, "The (physicists') Hermite polynomial.");
orthogonal!(laguerre, "The Laguerre polynomial.");

/// The generalized Laguerre polynomial `L_n^alpha(var)`.
///
/// Tier R: a pure function of its arguments.
///
/// # Errors
///
/// Raises `OverflowError` when `alpha` does not fit the exact `i128` rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn generalized_laguerre(n: u32, alpha: &Bound<'_, PyAny>, var: &str) -> PyResult<Option<Expr>> {
    Ok(Expr::wrap_option(
        axeyum_cas::orthopoly::generalized_laguerre(n, rational_arg(alpha)?, var),
    ))
}

/// The Gegenbauer (ultraspherical) polynomial `C_n^lambda(var)`.
///
/// Tier R: a pure function of its arguments.
///
/// # Errors
///
/// Raises `OverflowError` when `lambda` does not fit the exact `i128` rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gegenbauer(n: u32, weight: &Bound<'_, PyAny>, var: &str) -> PyResult<Option<Expr>> {
    Ok(Expr::wrap_option(axeyum_cas::orthopoly::gegenbauer(
        n,
        rational_arg(weight)?,
        var,
    )))
}

/// The Jacobi polynomial `P_n^(alpha, beta)(var)`.
///
/// Tier R: a pure function of its arguments.
///
/// # Errors
///
/// Raises `OverflowError` when a parameter does not fit the exact `i128`
/// rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn jacobi(
    n: u32,
    alpha: &Bound<'_, PyAny>,
    beta: &Bound<'_, PyAny>,
    var: &str,
) -> PyResult<Option<Expr>> {
    Ok(Expr::wrap_option(axeyum_cas::orthopoly::jacobi(
        n,
        rational_arg(alpha)?,
        rational_arg(beta)?,
        var,
    )))
}

/// The Gamma function at an exact rational, or `None` outside the closed-form
/// fragment.
///
/// Tier R: a pure function of `x`. Closed forms exist at the positive integers
/// and the half-integers; everything else is `None`, which is *no closed form
/// here* rather than an error.
///
/// # Errors
///
/// Raises `OverflowError` when `x` does not fit the exact `i128` rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gamma(x: &Bound<'_, PyAny>) -> PyResult<Option<Expr>> {
    Ok(Expr::wrap_option(axeyum_cas::special::gamma(rational_arg(
        x,
    )?)))
}

/// The Beta function `B(x, y)`, or `None` outside the closed-form fragment.
///
/// Tier R: a pure function of its arguments.
///
/// # Errors
///
/// Raises `OverflowError` when an argument does not fit the exact `i128`
/// rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn beta(x: &Bound<'_, PyAny>, y: &Bound<'_, PyAny>) -> PyResult<Option<Expr>> {
    Ok(Expr::wrap_option(axeyum_cas::special::beta(
        rational_arg(x)?,
        rational_arg(y)?,
    )))
}

/// The Riemann zeta function at an integer, or `None` where no closed form is
/// known.
///
/// Tier R: a pure function of `s`. `zeta(2)` is exact; `zeta(3)` is `None`
/// because Apery's constant has no closed form in this fragment — a decided
/// answer, not a decline to compute.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn zeta(s: i64) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::special::zeta(s))
}

/// The polygamma function `psi^(m)(1)`, or `None`.
///
/// Tier R: a pure function of `m`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn polygamma_at_one(m: u32) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::special::polygamma_at_one(m))
}

/// The Dirichlet eta function at an integer, or `None`.
///
/// Tier R: a pure function of `s`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn dirichlet_eta(s: i64) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::special::dirichlet_eta(s))
}

/// The Dirichlet lambda function at an integer, or `None`.
///
/// Tier R: a pure function of `s`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn dirichlet_lambda(s: i64) -> Option<Expr> {
    Expr::wrap_option(axeyum_cas::special::dirichlet_lambda(s))
}

/// Reads `[(x, y), ...]` as exact rational sample points.
///
/// # Errors
///
/// Raises `OverflowError` when a coordinate does not fit the exact `i128`
/// rational.
fn points_arg(
    points: &Bound<'_, PyAny>,
) -> PyResult<Vec<(axeyum_ir::Rational, axeyum_ir::Rational)>> {
    points
        .try_iter()?
        .map(|item| {
            let item = item?;
            let x = item.get_item(0)?;
            let y = item.get_item(1)?;
            Ok((rational_arg(&x)?, rational_arg(&y)?))
        })
        .collect()
}

/// The Newton divided-difference coefficients of the interpolant through
/// `points`.
///
/// Tier R: a pure function of the sample. `None` for repeated abscissae or
/// exact-arithmetic overflow.
///
/// # Errors
///
/// Raises `OverflowError` when a coordinate does not fit the exact `i128`
/// rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn newton_divided_differences<'py>(
    py: Python<'py>,
    points: &Bound<'py, PyAny>,
) -> PyResult<Option<Vec<PyFraction<'py>>>> {
    let points = points_arg(points)?;
    axeyum_cas::newton_divided_differences(&points)
        .map(|coefficients| {
            coefficients
                .into_iter()
                .map(|value| rational::fraction(py, value))
                .collect::<PyResult<Vec<_>>>()
        })
        .transpose()
}

/// The Lagrange interpolating polynomial through `points`, in `var`.
///
/// Tier R: a pure function of the sample.
///
/// # Errors
///
/// Raises `OverflowError` when a coordinate does not fit the exact `i128`
/// rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn lagrange_interpolation(points: &Bound<'_, PyAny>, var: &str) -> PyResult<Option<Expr>> {
    let points = points_arg(points)?;
    Ok(Expr::wrap_option(axeyum_cas::lagrange_interpolation(
        &points, var,
    )))
}

/// The `[m/n]` Pade approximant of a Maclaurin series, as `P(var) / Q(var)`.
///
/// Tier R: a pure function of the coefficients. `None` when fewer than
/// `m + n + 1` coefficients are supplied, when the denominator system is
/// singular, or on exact overflow.
///
/// # Errors
///
/// Raises `OverflowError` when a coefficient does not fit the exact `i128`
/// rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn pade(series_coeffs: &Bound<'_, PyAny>, m: usize, n: usize, var: &str) -> PyResult<Option<Expr>> {
    let coefficients = crate::cas::ntheory::rational_vec_arg(series_coeffs)?;
    Ok(Expr::wrap_option(axeyum_cas::pade(
        &coefficients,
        m,
        n,
        var,
    )))
}

/// The `[m/n]` Pade approximant as raw coefficient vectors
/// `(numerator, denominator)`, ascending in degree, with `Q(0) == 1`.
///
/// Tier R. Exposed alongside [`pade`] because the coefficient vectors are what
/// a caller re-checks `P - Q * A == 0 (mod x ** (m + n + 1))` against.
///
/// # Errors
///
/// Raises `OverflowError` when a coefficient does not fit the exact `i128`
/// rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn pade_fraction<'py>(
    py: Python<'py>,
    series_coeffs: &Bound<'py, PyAny>,
    m: usize,
    n: usize,
) -> PyResult<Option<(Vec<PyFraction<'py>>, Vec<PyFraction<'py>>)>> {
    let coefficients = crate::cas::ntheory::rational_vec_arg(series_coeffs)?;
    let Some((numerator, denominator)) = axeyum_cas::pade_fraction(&coefficients, m, n) else {
        return Ok(None);
    };
    let render = |values: Vec<axeyum_ir::Rational>| {
        values
            .into_iter()
            .map(|value| rational::fraction(py, value))
            .collect::<PyResult<Vec<_>>>()
    };
    Ok(Some((render(numerator)?, render(denominator)?)))
}

/// Registers the special-function surface on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    macro_rules! add {
        ($($name:ident),* $(,)?) => {
            $(module.add_function(wrap_pyfunction!($name, module)?)?;)*
        };
    }
    add!(
        sinh,
        cosh,
        tanh,
        coth,
        sech,
        csch,
        asinh,
        acosh,
        atanh,
        chebyshev_t,
        chebyshev_u,
        legendre,
        hermite,
        laguerre,
        generalized_laguerre,
        gegenbauer,
        jacobi,
        gamma,
        beta,
        zeta,
        polygamma_at_one,
        dirichlet_eta,
        dirichlet_lambda,
        newton_divided_differences,
        lagrange_interpolation,
        pade,
        pade_fraction,
    );
    Ok(())
}
