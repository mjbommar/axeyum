//! `axeyum.cas` — integral and discrete transforms (tier R).
//!
//! Each of these is a table-driven exact transform over a recognised fragment.
//! `None` means *this input is outside the table*, which is a decided answer
//! about the fragment and not a failure to try harder: `laplace_transform` of an
//! expression it does not recognise declines rather than returning an unevaluated
//! form, so a caller can never mistake a placeholder for a result.

use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::cas::expr::Expr;

/// Binds `fn(&CasExpr, &str, &str) -> Option<CasExpr>`.
macro_rules! transform {
    ($name:ident, $from:ident, $to:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a pure function of its arguments. `None` is *outside the
        /// transform table*, never an error.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $name(py: Python<'_>, expr: &Expr, $from: &str, $to: &str) -> Option<Expr> {
            Expr::wrap_option(py.detach(|| axeyum_cas::$name(expr.inner(), $from, $to)))
        }
    };
}

transform!(
    laplace_transform,
    t,
    s,
    "The Laplace transform of `expr` from `t` to `s`."
);
transform!(
    inverse_laplace,
    s,
    t,
    "The inverse Laplace transform of `expr` from `s` to `t`."
);
transform!(
    z_transform,
    n,
    z,
    "The unilateral Z-transform of the signal `expr` from `n` to `z`."
);
transform!(
    inverse_z_transform,
    z,
    n,
    "The inverse Z-transform of `expr` from `z` to `n`."
);

/// The Laurent series of `expr` in `var` to `order`, including negative powers.
///
/// Tier R: a pure function of its arguments. `None` when the expansion leaves
/// the fragment or overflows.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn laurent_series(py: Python<'_>, expr: &Expr, var: &str, order: usize) -> Option<Expr> {
    Expr::wrap_option(py.detach(|| axeyum_cas::laurent_series(expr.inner(), var, order)))
}

/// The compositional inverse (series reversion) of `expr` to `order`.
///
/// Tier R: a pure function of its arguments. Reversion needs a zero constant
/// term and a nonzero linear term; anything else is `None`, which is a
/// statement about the series and not a budget.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn series_reversion(py: Python<'_>, expr: &Expr, var: &str, order: usize) -> Option<Expr> {
    Expr::wrap_option(py.detach(|| axeyum_cas::series_reversion(expr.inner(), var, order)))
}

/// Registers the transform surface on `module`.
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
        laplace_transform,
        inverse_laplace,
        z_transform,
        inverse_z_transform,
        laurent_series,
        series_reversion,
    );
    Ok(())
}
