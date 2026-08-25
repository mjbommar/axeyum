//! `axeyum.cas.certify.sturm` — exact real-root counting and interval enclosures.
//!
//! Checker-shaped pure functions with no certificate object: a Sturm count *is*
//! its own evidence, and `None` means the exact arithmetic left `i128`.
//!
//! Three interval types exist in `axeyum-cas` and they are not
//! interchangeable. This module binds `interval_arith::Interval` as
//! `Interval` — the enclosure primitive. `sets::Interval` is `SetInterval`
//! here, and `lib::RealInterval` (what `solve_polynomial_inequality` returns) is
//! `cas.RealInterval`.

use axeyum_cas::interval_arith::{Interval as CasInterval, evaluate_polynomial};
use axeyum_cas::sets::Interval as CasSetInterval;
use axeyum_cas::sturm;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::rational;

/// A closed real interval with exact rational endpoints.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Interval")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    inner: CasInterval,
}

impl Interval {
    /// Wraps a Rust interval.
    fn wrap(inner: CasInterval) -> Self {
        Self { inner }
    }

    /// Wraps an optional Rust interval.
    fn wrap_option(value: Option<CasInterval>) -> Option<Self> {
        value.map(Self::wrap)
    }
}

#[pymethods]
impl Interval {
    /// `[a, b]`, or `None` when `a > b`.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when an endpoint is not an exact rational.
    #[new]
    fn new(a: &Bound<'_, PyAny>, b: &Bound<'_, PyAny>) -> PyResult<Option<Interval>> {
        Ok(Interval::wrap_option(CasInterval::new(
            rational::from_py(a)?,
            rational::from_py(b)?,
        )))
    }

    /// The single-point interval `[a, a]`.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when `a` is not an exact rational.
    #[staticmethod]
    fn degenerate(a: &Bound<'_, PyAny>) -> PyResult<Interval> {
        Ok(Interval::wrap(CasInterval::degenerate(rational::from_py(
            a,
        )?)))
    }

    /// The lower endpoint.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    #[getter]
    fn lower<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        rational::fraction(py, self.inner.lower())
    }

    /// The upper endpoint.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    #[getter]
    fn upper<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        rational::fraction(py, self.inner.upper())
    }

    /// `upper - lower`.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    fn width<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        rational::fraction(py, self.inner.width())
    }

    /// The midpoint.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    fn midpoint<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        rational::fraction(py, self.inner.midpoint())
    }

    /// Whether `x` lies in the interval.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when `x` is not an exact rational.
    fn contains(&self, x: &Bound<'_, PyAny>) -> PyResult<bool> {
        Ok(self.inner.contains(rational::from_py(x)?))
    }

    /// Whether `other` is contained in this interval.
    fn contains_interval(&self, other: &Interval) -> bool {
        self.inner.contains_interval(&other.inner)
    }

    /// The sum enclosure, or `None` on overflow.
    fn add(&self, other: &Interval) -> Option<Interval> {
        Interval::wrap_option(self.inner.add(&other.inner))
    }

    /// The difference enclosure, or `None` on overflow.
    fn sub(&self, other: &Interval) -> Option<Interval> {
        Interval::wrap_option(self.inner.sub(&other.inner))
    }

    /// The product enclosure, or `None` on overflow.
    fn mul(&self, other: &Interval) -> Option<Interval> {
        Interval::wrap_option(self.inner.mul(&other.inner))
    }

    /// The negation enclosure, or `None` on overflow.
    fn neg(&self) -> Option<Interval> {
        Interval::wrap_option(self.inner.neg())
    }

    /// The quotient enclosure, or `None`.
    ///
    /// **`None` when the divisor straddles zero is the soundness guard, not an
    /// error.** No finite interval encloses `1/[-1, 1]`, so returning anything
    /// there would be a wrong enclosure; declining is the only sound answer, and
    /// the same `None` also covers an overflow.
    fn div(&self, other: &Interval) -> Option<Interval> {
        Interval::wrap_option(self.inner.div(&other.inner))
    }

    /// The `n`-th power enclosure, or `None` on overflow.
    fn pow(&self, n: u32) -> Option<Interval> {
        Interval::wrap_option(self.inner.pow(n))
    }

    /// The intersection, or `None` when the intervals are disjoint.
    fn intersection(&self, other: &Interval) -> Option<Interval> {
        Interval::wrap_option(self.inner.intersection(&other.inner))
    }

    /// The convex hull, or `None` on overflow.
    fn hull(&self, other: &Interval) -> Option<Interval> {
        Interval::wrap_option(self.inner.hull(&other.inner))
    }

    /// The absolute-value enclosure, or `None` on overflow.
    fn abs(&self) -> Option<Interval> {
        Interval::wrap_option(self.inner.abs())
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value -- an entire expression tree or certificate -- to
        // compare it and then drops it, and builds a `TypeError` object for the
        // ordinary `NotImplemented` case. `frozen` makes `Bound::get` a borrow
        // with no runtime borrow check at all.
        other
            .cast::<Interval>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        let lower = self.inner.lower();
        let upper = self.inner.upper();
        format!(
            "Interval({}/{}, {}/{})",
            lower.numerator(),
            lower.denominator(),
            upper.numerator(),
            upper.denominator()
        )
    }
}

/// An interval from `axeyum_cas::sets`, with open/closed bounds.
///
/// Named apart from [`Interval`] deliberately: the two are different types with
/// different guarantees, and the crate's own inventory flags the collision.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "SetInterval")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SetInterval {
    inner: CasSetInterval,
}

#[pymethods]
impl SetInterval {
    /// `[a, b]`.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when an endpoint is not an exact rational.
    #[staticmethod]
    fn closed(a: &Bound<'_, PyAny>, b: &Bound<'_, PyAny>) -> PyResult<SetInterval> {
        Ok(SetInterval {
            inner: CasSetInterval::closed(rational::from_py(a)?, rational::from_py(b)?),
        })
    }

    /// `(a, b)`.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when an endpoint is not an exact rational.
    #[staticmethod]
    fn open(a: &Bound<'_, PyAny>, b: &Bound<'_, PyAny>) -> PyResult<SetInterval> {
        Ok(SetInterval {
            inner: CasSetInterval::open(rational::from_py(a)?, rational::from_py(b)?),
        })
    }

    /// All of the reals.
    #[staticmethod]
    fn universe() -> SetInterval {
        SetInterval {
            inner: CasSetInterval::universe(),
        }
    }

    /// Whether the interval contains no points.
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Whether `x` lies in the interval.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when `x` is not an exact rational.
    fn contains(&self, x: &Bound<'_, PyAny>) -> PyResult<bool> {
        Ok(self.inner.contains(rational::from_py(x)?))
    }

    fn __repr__(&self) -> String {
        "SetInterval(...)".to_owned()
    }
}

/// The exact number of distinct real roots of `p` in `[lower, upper]`.
///
/// `p` is dense, lowest degree first. `None` means the exact arithmetic left
/// `i128` — an honest undecided, never a zero.
///
/// # Errors
///
/// Raises `ValueError` when a coefficient or endpoint is not an exact rational.
#[pyfunction]
fn count_real_roots_in(
    p: &Bound<'_, PyAny>,
    lower: &Bound<'_, PyAny>,
    upper: &Bound<'_, PyAny>,
) -> PyResult<Option<usize>> {
    let coefficients = rational::vec_from_py(p)?;
    Ok(sturm::count_real_roots_in(
        &coefficients,
        rational::from_py(lower)?,
        rational::from_py(upper)?,
    ))
}

/// Isolating intervals, one per distinct real root, ascending.
///
/// # Errors
///
/// Raises `ValueError` when a coefficient is not an exact rational.
#[pyfunction]
fn isolate_real_roots<'py>(
    py: Python<'py>,
    p: &Bound<'py, PyAny>,
) -> PyResult<Option<Vec<(Bound<'py, PyAny>, Bound<'py, PyAny>)>>> {
    let coefficients = rational::vec_from_py(p)?;
    sturm::isolate_real_roots(&coefficients)
        .map(|intervals| {
            intervals
                .into_iter()
                .map(|(lower, upper)| {
                    Ok((
                        rational::fraction(py, lower)?,
                        rational::fraction(py, upper)?,
                    ))
                })
                .collect::<PyResult<Vec<_>>>()
        })
        .transpose()
}

/// Rational approximations of every real root, each within `width`.
///
/// `width` is the caller's explicit resource limit; there is no hidden default.
///
/// # Errors
///
/// Raises `ValueError` when a coefficient or `width` is not an exact rational.
#[pyfunction]
fn approximate_real_roots<'py>(
    py: Python<'py>,
    p: &Bound<'py, PyAny>,
    width: &Bound<'py, PyAny>,
) -> PyResult<Option<Vec<Bound<'py, PyAny>>>> {
    let coefficients = rational::vec_from_py(p)?;
    let width = rational::from_py(width)?;
    sturm::approximate_real_roots(&coefficients, width)
        .map(|roots| {
            roots
                .into_iter()
                .map(|root| rational::fraction(py, root))
                .collect::<PyResult<Vec<_>>>()
        })
        .transpose()
}

/// The interval enclosure of a dense polynomial over `x`.
///
/// # Errors
///
/// Raises `ValueError` when a coefficient is not an exact rational.
#[pyfunction]
fn evaluate_polynomial_over(coeffs: &Bound<'_, PyAny>, x: &Interval) -> PyResult<Option<Interval>> {
    let coefficients = rational::vec_from_py(coeffs)?;
    Ok(Interval::wrap_option(evaluate_polynomial(
        &coefficients,
        &x.inner,
    )))
}

/// Registers the `sturm` route on `parent`.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let module = PyModule::new(parent.py(), "axeyum._native.cas.certify.sturm")?;
    module.add_class::<Interval>()?;
    module.add_class::<SetInterval>()?;
    module.add_function(wrap_pyfunction!(count_real_roots_in, &module)?)?;
    module.add_function(wrap_pyfunction!(isolate_real_roots, &module)?)?;
    module.add_function(wrap_pyfunction!(approximate_real_roots, &module)?)?;
    module.add_function(wrap_pyfunction!(evaluate_polynomial_over, &module)?)?;
    parent.add("sturm", &module)?;
    Ok(())
}
