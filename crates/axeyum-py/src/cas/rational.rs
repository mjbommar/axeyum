//! `axeyum.cas.Rational` — the exact `i128` rational the whole CAS speaks.
//!
//! `axeyum-cas` does not re-export [`axeyum_ir::Rational`], so this binding
//! wraps it from `axeyum-ir` directly (inventory §0.4). Every coefficient in the
//! CAS is a checked `i128` pair: an overflow surfaces as `None`, never as a
//! wrong answer, and that is why nothing here silently widens to `BigInt`.

use axeyum_ir::Rational as IrRational;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::stub_types::PyFraction;

/// An exact rational number, normalized, with an `i128` numerator and
/// denominator.
///
/// Constructing one with a zero denominator raises `ValueError`:
/// `axeyum_ir::Rational::new` panics there, so the binding goes through
/// `checked_new` (inventory §0.6).
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Rational")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rational {
    inner: IrRational,
}

impl Rational {
    /// Wraps an IR rational.
    pub(crate) fn wrap(inner: IrRational) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Rational {
    /// `Rational(num, den=1)`.
    #[new]
    #[pyo3(signature = (num, den = 1))]
    fn new(num: i128, den: i128) -> PyResult<Self> {
        checked(num, den).map(Self::wrap).ok_or_else(|| {
            PyValueError::new_err(format!(
                "Rational({num}, {den}): denominator must be nonzero and the normalized \
                 pair must fit in i128"
            ))
        })
    }

    /// The normalized numerator (carries the sign).
    #[getter]
    fn numerator(&self) -> i128 {
        self.inner.numerator()
    }

    /// The normalized denominator (always positive).
    #[getter]
    fn denominator(&self) -> i128 {
        self.inner.denominator()
    }

    /// Whether the denominator is `1`.
    fn is_integer(&self) -> bool {
        self.inner.is_integer()
    }

    /// Whether the value is exactly zero.
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// The same value as a `fractions.Fraction`.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while importing `fractions`.
    fn to_fraction<'py>(&self, py: Python<'py>) -> PyResult<PyFraction<'py>> {
        fraction(py, self.inner)
    }

    /// Builds a [`Rational`] from anything with `numerator`/`denominator` —
    /// a Python `int`, a `fractions.Fraction`, or another [`Rational`].
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when the pair does not fit in `i128` or the
    /// denominator is zero, and `TypeError` for an object with no such fields.
    #[staticmethod]
    fn coerce(value: RationalLike<'_>) -> PyResult<Self> {
        from_py(value.as_any()).map(Self::wrap)
    }

    fn __repr__(&self) -> String {
        format!(
            "Rational({}, {})",
            self.inner.numerator(),
            self.inner.denominator()
        )
    }

    fn __str__(&self) -> String {
        if self.inner.is_integer() {
            format!("{}", self.inner.numerator())
        } else {
            format!("{}/{}", self.inner.numerator(), self.inner.denominator())
        }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        from_py(other).is_ok_and(|other| other == self.inner)
    }

    fn __hash__(&self) -> isize {
        // Agrees with `__eq__` for the values a Python `int`/`Fraction` can hold
        // by hashing the normalized pair, which is what `__eq__` compares.
        let (num, den) = (self.inner.numerator(), self.inner.denominator());
        #[allow(clippy::cast_possible_truncation)]
        {
            (num as isize).wrapping_mul(31).wrapping_add(den as isize)
        }
    }
}

/// `Rational::checked_new` with the zero denominator ALSO guarded.
///
/// `checked_new` is documented as the overflow-graceful counterpart of `new`,
/// but it keeps `new`'s `assert!(den != 0)` — measured 2026-08-24, a `den == 0`
/// reaches an `assert!` in `axeyum-ir/src/rational.rs:69` and aborts as a
/// `PanicException`, not as the `None` the name suggests. Wrapping `rat` in
/// `checked_new` alone would therefore NOT have stopped the documented panic;
/// the explicit test below it is what does.
pub(crate) fn checked(num: i128, den: i128) -> Option<IrRational> {
    if den == 0 {
        return None;
    }
    IrRational::checked_new(num, den)
}

/// `fractions.Fraction(numerator, denominator)` for an IR rational.
///
/// # Errors
///
/// Propagates any Python error raised while importing `fractions`.
pub(crate) fn fraction(py: Python<'_>, value: IrRational) -> PyResult<PyFraction<'_>> {
    PyModule::import(py, "fractions")?
        .getattr("Fraction")?
        .call1((value.numerator(), value.denominator()))
        .map(PyFraction::new)
}

/// `fractions.Fraction` for an optional IR rational; `None` stays `None`.
///
/// # Errors
///
/// Propagates any Python error raised while importing `fractions`.
pub(crate) fn optional_fraction(
    py: Python<'_>,
    value: Option<IrRational>,
) -> PyResult<Option<PyFraction<'_>>> {
    value.map(|value| fraction(py, value)).transpose()
}

/// Reads an IR rational out of any Python object exposing `numerator` and
/// `denominator` — `int`, `fractions.Fraction`, and [`Rational`] all do.
///
/// # Errors
///
/// Raises `ValueError` when the pair does not fit in `i128` or normalizes with a
/// zero denominator; propagates the attribute error otherwise.
pub(crate) fn from_py(value: &Bound<'_, PyAny>) -> PyResult<IrRational> {
    if let Ok(wrapped) = value.extract::<Rational>() {
        return Ok(wrapped.inner);
    }
    let numerator: i128 = value
        .getattr("numerator")
        .map_err(|_| {
            PyValueError::new_err(format!(
                "expected an int, a fractions.Fraction, or a cas.Rational; got {}",
                value
                    .get_type()
                    .name()
                    .map_or_else(|_| "<unknown>".to_owned(), |name| name.to_string())
            ))
        })?
        .extract()
        .map_err(|_| PyValueError::new_err("numerator does not fit in i128"))?;
    let denominator: i128 = value
        .getattr("denominator")?
        .extract()
        .map_err(|_| PyValueError::new_err("denominator does not fit in i128"))?;
    checked(numerator, denominator).ok_or_else(|| {
        PyValueError::new_err("rational has a zero denominator or does not normalize inside i128")
    })
}

/// Reads a list of rationals.
///
/// # Errors
///
/// Propagates the per-element conversion error.
pub(crate) fn vec_from_py(values: &Bound<'_, PyAny>) -> PyResult<Vec<IrRational>> {
    values.try_iter()?.map(|item| from_py(&item?)).collect()
}

/// Anything this crate accepts where an exact rational is wanted: a Python
/// `int`, a `fractions.Fraction`, or a [`Rational`].
///
/// [`from_py`] reads `numerator`/`denominator` off the object, so the Rust
/// parameter has to be `&Bound<'_, PyAny>` and the derived stub would say
/// `typing.Any` -- true, and useless. This wrapper changes nothing at run time
/// (it is the same handle) and makes the stub name the three types the error
/// message already names.
pub(crate) struct RationalLike<'py>(Bound<'py, PyAny>);

impl<'py> RationalLike<'py> {
    /// The wrapped object, to read `numerator`/`denominator` from.
    pub(crate) fn as_any(&self) -> &Bound<'py, PyAny> {
        &self.0
    }
}

impl<'py> FromPyObject<'_, 'py> for RationalLike<'py> {
    type Error = PyErr;

    fn extract(object: pyo3::Borrowed<'_, 'py, PyAny>) -> Result<Self, Self::Error> {
        Ok(Self(object.to_owned()))
    }
}

#[cfg(feature = "stub-gen")]
impl pyo3_stub_gen::PyStubType for RationalLike<'_> {
    fn type_input() -> pyo3_stub_gen::TypeInfo {
        use pyo3_stub_gen::PyStubType;
        <i128 as PyStubType>::type_input()
            | <PyFraction<'_> as PyStubType>::type_output()
            | <Rational as PyStubType>::type_output()
    }

    fn type_output() -> pyo3_stub_gen::TypeInfo {
        Self::type_input()
    }
}
