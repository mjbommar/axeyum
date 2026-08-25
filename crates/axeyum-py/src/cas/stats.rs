//! `axeyum.cas` — exact descriptive statistics over the rationals (tier R).
//!
//! Nothing here is floating point. The data are exact `i128` rationals, so
//! `variance([1, 2, 3, 4])` is the fraction `5/4` and not `1.25`, and a datum
//! that does not fit the exact pair raises `OverflowError` rather than being
//! rounded into range.
//!
//! `None` means *the statistic is not defined for this sample* (an empty list,
//! or mismatched lengths for `covariance`) or *the exact arithmetic overflowed*.
//! Both are answers; neither is an error.

use pyo3::prelude::*;

use crate::stub_types::PyFraction;
use pyo3::types::{PyAny, PyModule};

use crate::cas::ntheory::{rational_arg, rational_vec_arg};
use crate::cas::rational;

/// Binds `fn(&[Rational]) -> Option<Rational>`.
macro_rules! sample_statistic {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a pure function of the sample. `None` is *undefined for this
        /// sample* or exact-arithmetic overflow.
        ///
        /// # Errors
        ///
        /// Raises `OverflowError` when a datum does not fit the exact `i128`
        /// rational, and `ValueError`/`TypeError` for a value that is not an
        /// exact rational at all.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $name<'py>(
            py: Python<'py>,
            data: &Bound<'py, PyAny>,
        ) -> PyResult<Option<PyFraction<'py>>> {
            let data = rational_vec_arg(data)?;
            rational::optional_fraction(py, axeyum_cas::stats::$name(&data))
        }
    };
}

sample_statistic!(mean, "The arithmetic mean.");
sample_statistic!(
    median,
    "The median; the mean of the two middle values for an even sample."
);
sample_statistic!(variance, "The population variance (divisor `n`).");
sample_statistic!(sample_variance, "The sample variance (divisor `n - 1`).");

/// Every most-frequent value, ascending; the empty list for empty data.
///
/// Tier R: a pure function of the sample. A sample with no repeats is
/// multimodal, so this returns every value — it never picks one.
///
/// # Errors
///
/// Raises `OverflowError` when a datum does not fit the exact `i128` rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn mode<'py>(py: Python<'py>, data: &Bound<'py, PyAny>) -> PyResult<Vec<PyFraction<'py>>> {
    let data = rational_vec_arg(data)?;
    axeyum_cas::stats::mode(&data)
        .into_iter()
        .map(|value| rational::fraction(py, value))
        .collect()
}

/// The population covariance of two equal-length samples.
///
/// Tier R: a pure function of the samples. `None` for mismatched lengths, an
/// empty sample, or overflow.
///
/// # Errors
///
/// Raises `OverflowError` when a datum does not fit the exact `i128` rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn covariance<'py>(
    py: Python<'py>,
    xs: &Bound<'py, PyAny>,
    ys: &Bound<'py, PyAny>,
) -> PyResult<Option<PyFraction<'py>>> {
    let xs = rational_vec_arg(xs)?;
    let ys = rational_vec_arg(ys)?;
    rational::optional_fraction(py, axeyum_cas::stats::covariance(&xs, &ys))
}

/// The exact rational a Python value denotes, as a `fractions.Fraction`.
///
/// Tier R. Exposed because the boundary rule this module documents — a value
/// too large for the exact `i128` pair is an `OverflowError`, not a
/// `ValueError` — is otherwise only observable through a statistic.
///
/// # Errors
///
/// Raises `OverflowError` beyond `i128`, `ValueError`/`TypeError` for a value
/// that is not an exact rational.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn exact_rational<'py>(py: Python<'py>, value: &Bound<'py, PyAny>) -> PyResult<PyFraction<'py>> {
    rational::fraction(py, rational_arg(value)?)
}

/// Registers the statistics surface on `module`.
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
        mean,
        median,
        mode,
        variance,
        sample_variance,
        covariance,
        exact_rational,
    );
    Ok(())
}
