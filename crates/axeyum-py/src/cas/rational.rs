//! Exact Python rationals backed by the existing small/promoted Rust carrier.

use axeyum_arith::big::{BigInt, BigRational, Zero};
use axeyum_ir::Rational as IrRational;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyBytes, PyDict, PyInt, PyModule};

use crate::stub_types::{PyBigInt, PyFraction};

const MAX_INTEGER_BITS: u64 = 16_384;

/// An exact rational number with a positive denominator. Integer transport
/// supports up to 16,384 bits per input or result component.
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
    #[pyo3(signature = (num, den = None))]
    fn new(num: &Bound<'_, PyInt>, den: Option<&Bound<'_, PyInt>>) -> PyResult<Self> {
        from_pair(num.as_any(), den.map(Bound::as_any)).map(Self::wrap)
    }

    /// The normalized numerator (carries the sign).
    #[getter]
    fn numerator<'py>(&self, py: Python<'py>) -> PyResult<PyBigInt<'py>> {
        to_integer(py, &self.inner.numerator_big()).map(PyBigInt::new)
    }

    /// The normalized denominator (always positive).
    #[getter]
    fn denominator<'py>(&self, py: Python<'py>) -> PyResult<PyBigInt<'py>> {
        to_integer(py, &self.inner.denominator_big()).map(PyBigInt::new)
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
    /// Raises `ValueError` when integer transport exceeds its bit limit or the
    /// denominator is zero, and `TypeError` for an object with no such fields.
    #[staticmethod]
    fn coerce(value: RationalLike<'_>) -> PyResult<Self> {
        from_py(value.as_any()).map(Self::wrap)
    }

    fn __repr__(&self) -> String {
        format!(
            "Rational({}, {})",
            self.inner.numerator_big(),
            self.inner.denominator_big()
        )
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        from_py(other).is_ok_and(|other| other == self.inner)
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<isize> {
        fraction(py, self.inner)?.into_bound().hash()
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
        .call1((
            to_integer(py, &value.numerator_big())?,
            to_integer(py, &value.denominator_big())?,
        ))
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
/// Raises `ValueError` when integer transport exceeds its bit limit or has a
/// zero denominator; propagates the attribute error otherwise.
pub(crate) fn from_py(value: &Bound<'_, PyAny>) -> PyResult<IrRational> {
    if let Ok(wrapped) = value.extract::<Rational>() {
        return Ok(wrapped.inner);
    }
    if value.is_instance_of::<PyInt>() {
        return from_pair(value, None);
    }
    from_pair(
        &value.getattr("numerator")?,
        Some(&value.getattr("denominator")?),
    )
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

/// Exact bounded integer pair transport. Omitted denominator means one.
pub(crate) fn from_pair(
    num: &Bound<'_, PyAny>,
    den: Option<&Bound<'_, PyAny>>,
) -> PyResult<IrRational> {
    let numerator = from_integer(num)?;
    let denominator = den
        .map(from_integer)
        .transpose()?
        .unwrap_or_else(|| BigInt::from(1));
    if denominator.is_zero() {
        return Err(PyValueError::new_err(
            "rational denominator must be nonzero",
        ));
    }
    IrRational::from_big_rational(&BigRational::new(numerator, denominator))
        .ok_or_else(|| PyValueError::new_err("rational interning resource limit exceeded"))
}

fn from_integer(value: &Bound<'_, PyAny>) -> PyResult<BigInt> {
    let integer = value.cast::<PyInt>()?;
    let integer_type = PyModule::import(value.py(), "builtins")?.getattr("int")?;
    let bits: u64 = integer_type
        .getattr("bit_length")?
        .call1((integer,))?
        .extract()?;
    if bits > MAX_INTEGER_BITS {
        return Err(PyValueError::new_err(
            "rational integer transport exceeds 16384 bits",
        ));
    }
    let bytes = usize::try_from(bits.div_ceil(8) + 1)
        .map_err(|_| PyValueError::new_err("rational byte count exceeds platform limits"))?;
    let keywords = PyDict::new(value.py());
    keywords.set_item("signed", true)?;
    let encoded = integer_type
        .getattr("to_bytes")?
        .call((integer, bytes, "little"), Some(&keywords))?;
    Ok(BigInt::from_signed_bytes_le(
        encoded.cast::<PyBytes>()?.as_bytes(),
    ))
}

fn to_integer<'py>(py: Python<'py>, value: &BigInt) -> PyResult<Bound<'py, PyAny>> {
    if value.bits() > MAX_INTEGER_BITS {
        return Err(PyValueError::new_err(
            "rational integer transport exceeds 16384 bits",
        ));
    }
    let keywords = PyDict::new(py);
    keywords.set_item("signed", true)?;
    PyModule::import(py, "builtins")?
        .getattr("int")?
        .call_method(
            "from_bytes",
            (PyBytes::new(py, &value.to_signed_bytes_le()), "little"),
            Some(&keywords),
        )
}
