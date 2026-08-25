//! `axeyum.cas` — real algebraic numbers and sets of reals (tier R).
//!
//! An [`AlgebraicReal`] is **not** a float. It is a minimal polynomial over the
//! rationals plus an isolating interval, which is the representation that makes
//! equality decidable; `to_float` exists for display and is the only lossy thing
//! in the module. `refine` narrows the interval on demand, so a caller decides
//! how much precision to pay for rather than inheriting a default.
//!
//! [`RealSet`] is the normalized union of disjoint intervals, so structural
//! equality *is* set equality — `is_equal` and `==` agree by construction.

use axeyum_cas::AlgebraicReal as CasAlgebraicReal;
use axeyum_cas::sets::RealSet as CasRealSet;
use pyo3::prelude::*;

use crate::stub_types::PyFraction;
use pyo3::types::{PyAny, PyModule};

use crate::cas::certify::sturm::SetInterval;
use crate::cas::expr::Expr;
use crate::cas::ntheory::{rational_arg, rational_vec_arg};
use crate::cas::rational;

/// A real algebraic number: a minimal polynomial plus an isolating interval.
///
/// Tier R: owned plain data. Every operation is exact; `to_float` is the single
/// lossy accessor and is named so.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "AlgebraicReal")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlgebraicReal {
    inner: CasAlgebraicReal,
}

impl AlgebraicReal {
    /// Wraps a Rust algebraic real.
    pub(crate) fn wrap(inner: CasAlgebraicReal) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl AlgebraicReal {
    /// The minimal polynomial as exact coefficients, lowest degree first.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fractions.
    #[getter]
    fn minimal_polynomial<'py>(&self, py: Python<'py>) -> PyResult<Vec<PyFraction<'py>>> {
        self.inner
            .minimal_polynomial()
            .iter()
            .map(|value| rational::fraction(py, *value))
            .collect()
    }

    /// The degree of the minimal polynomial.
    #[getter]
    fn degree(&self) -> usize {
        self.inner.degree()
    }

    /// The isolating interval `(lower, upper)` containing exactly this root.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fractions.
    #[getter]
    fn isolating_interval<'py>(
        &self,
        py: Python<'py>,
    ) -> PyResult<(PyFraction<'py>, PyFraction<'py>)> {
        let (lower, upper) = self.inner.isolating_interval();
        Ok((
            rational::fraction(py, lower)?,
            rational::fraction(py, upper)?,
        ))
    }

    /// The exact rational value when this number is rational, else `None`.
    ///
    /// `None` is a decided answer — the number is irrational — not a decline.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    fn rational_value<'py>(&self, py: Python<'py>) -> PyResult<Option<PyFraction<'py>>> {
        rational::optional_fraction(py, self.inner.rational_value())
    }

    /// The same number with an isolating interval narrower than `width`, or
    /// `None` when the exact arithmetic overflows.
    ///
    /// # Errors
    ///
    /// Raises `OverflowError` when `width` does not fit the exact `i128`
    /// rational.
    fn refine(&self, width: &Bound<'_, PyAny>) -> PyResult<Option<AlgebraicReal>> {
        Ok(self
            .inner
            .refine(rational_arg(width)?)
            .map(AlgebraicReal::wrap))
    }

    /// A `float` near this number. The only lossy accessor here.
    fn to_float(&self) -> f64 {
        self.inner.to_f64()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value to compare it and then drops it.
        other
            .cast::<AlgebraicReal>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "AlgebraicReal(degree={}, approx={})",
            self.inner.degree(),
            self.inner.to_f64()
        )
    }
}

/// Every real root of a rational polynomial given by dense coefficients, lowest
/// degree first, ascending.
///
/// Tier R: a pure function of the coefficients. `None` is exact-arithmetic
/// overflow.
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
fn algebraic_real_roots(coeffs: &Bound<'_, PyAny>) -> PyResult<Option<Vec<AlgebraicReal>>> {
    let coeffs = rational_vec_arg(coeffs)?;
    Ok(axeyum_cas::algebraic::real_roots(&coeffs)
        .map(|roots| roots.into_iter().map(AlgebraicReal::wrap).collect()))
}

/// Every real root of `expr` in `var` as an exact algebraic number, ascending.
///
/// Tier R: a pure function of its arguments. `None` when `expr` is not a
/// univariate rational polynomial in `var`, or on overflow.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn real_roots(py: Python<'_>, expr: &Expr, var: &str) -> Option<Vec<AlgebraicReal>> {
    py.detach(|| axeyum_cas::real_roots(expr.inner(), var))
        .map(|roots| roots.into_iter().map(AlgebraicReal::wrap).collect())
}

/// A subset of the real line: a normalized ascending union of disjoint
/// intervals.
///
/// Tier R: owned plain data. The normal form is an invariant of every
/// constructor here, which is why `==` decides set equality and not just
/// structural sameness.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "RealSet")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RealSet {
    inner: CasRealSet,
}

impl RealSet {
    /// Wraps a Rust real set.
    fn wrap(inner: CasRealSet) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl RealSet {
    /// The empty set.
    #[staticmethod]
    fn empty() -> RealSet {
        RealSet::wrap(CasRealSet::empty())
    }

    /// The set denoted by one interval.
    #[staticmethod]
    fn interval(interval: &SetInterval) -> RealSet {
        RealSet::wrap(CasRealSet::interval(interval.inner()))
    }

    /// The singleton `{a}`.
    ///
    /// # Errors
    ///
    /// Raises `OverflowError` when `a` does not fit the exact `i128` rational.
    #[staticmethod]
    fn point(a: &Bound<'_, PyAny>) -> PyResult<RealSet> {
        Ok(RealSet::wrap(CasRealSet::point(rational_arg(a)?)))
    }

    /// All of the reals.
    #[staticmethod]
    fn universe() -> RealSet {
        RealSet::wrap(CasRealSet::universe())
    }

    /// The union of the given intervals, normalized.
    #[staticmethod]
    fn from_intervals(intervals: Vec<SetInterval>) -> RealSet {
        RealSet::wrap(CasRealSet::from_intervals(
            intervals.iter().map(SetInterval::inner).collect(),
        ))
    }

    /// The finite set of the given points; duplicates and order do not matter.
    ///
    /// # Errors
    ///
    /// Raises `OverflowError` when a point does not fit the exact `i128`
    /// rational.
    #[staticmethod]
    fn finite(points: &Bound<'_, PyAny>) -> PyResult<RealSet> {
        Ok(RealSet::wrap(axeyum_cas::finite_set(&rational_vec_arg(
            points,
        )?)))
    }

    /// The union.
    fn union(&self, other: &RealSet) -> RealSet {
        RealSet::wrap(self.inner.union(&other.inner))
    }

    /// The intersection.
    fn intersection(&self, other: &RealSet) -> RealSet {
        RealSet::wrap(self.inner.intersection(&other.inner))
    }

    /// The complement in the reals.
    fn complement(&self) -> RealSet {
        RealSet::wrap(self.inner.complement())
    }

    /// `self` minus `other`.
    fn difference(&self, other: &RealSet) -> RealSet {
        RealSet::wrap(self.inner.difference(&other.inner))
    }

    /// Whether `x` is a member.
    ///
    /// # Errors
    ///
    /// Raises `OverflowError` when `x` does not fit the exact `i128` rational.
    fn contains(&self, x: &Bound<'_, PyAny>) -> PyResult<bool> {
        Ok(self.inner.contains(rational_arg(x)?))
    }

    /// Whether the set has no points.
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Whether every point of `self` lies in `other`.
    fn is_subset(&self, other: &RealSet) -> bool {
        self.inner.is_subset(&other.inner)
    }

    /// Whether the two sets have the same points.
    fn is_equal(&self, other: &RealSet) -> bool {
        self.inner.is_equal(&other.inner)
    }

    /// The Lebesgue measure, or `None` when the set is unbounded or the exact
    /// sum overflows. Isolated points measure zero.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    fn measure<'py>(&self, py: Python<'py>) -> PyResult<Option<PyFraction<'py>>> {
        rational::optional_fraction(py, self.inner.measure())
    }

    /// The disjoint interval pieces, ascending.
    #[getter]
    fn intervals(&self) -> Vec<SetInterval> {
        self.inner
            .intervals()
            .iter()
            .copied()
            .map(SetInterval::wrap)
            .collect()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value to compare it and then drops it.
        other
            .cast::<RealSet>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!("RealSet(pieces={})", self.inner.intervals().len())
    }
}

/// Registers the algebraic-number and real-set surface on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<AlgebraicReal>()?;
    module.add_class::<RealSet>()?;
    module.add_function(wrap_pyfunction!(algebraic_real_roots, module)?)?;
    module.add_function(wrap_pyfunction!(real_roots, module)?)?;
    Ok(())
}
