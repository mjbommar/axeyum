//! Conversion of Axeyum IR values into Python objects.
//!
//! The rule is *sound, never inventive*: a variant is mapped to a Python type
//! only when the mapping is total and loses nothing.
//!
//! Since plan 02-A **every** `axeyum_ir::Value` variant has a typed Python
//! class. Nothing collapses to `repr` any more: an array arrives as
//! [`ArrayValue`] with its default and its overriding entries, a real-algebraic
//! number as its defining polynomial plus its isolating interval, a function
//! interpretation as [`FuncValue`] with its entry table. The old string
//! fallback was honest but useless — a caller could read it and could not
//! compute with it.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use axeyum_ir::{ArraySortKey, Rational, Sort, Value};
use pyo3::prelude::*;
use pyo3::types::{PyBool, PyBytes, PyDict, PyInt, PyList, PyModule, PyString, PyTuple};

use crate::ir::types::{PySort, SortError};
use crate::stub_types::{PyBigInt, PyFraction};

/// A bit-vector value: an unsigned integer together with the width it was
/// produced at.
///
/// The width is the part a plain Python `int` cannot carry, and it is exactly
/// what a caller needs to re-form the value as an SMT-LIB literal. The integer
/// itself is arbitrary-precision on the Python side, so `Value::Bv` (width
/// <= 128) and `Value::WideBv` (width > 128) converge on this one type — the
/// split in the Rust IR is a storage detail, not a semantic one.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "BvValue")]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BvValue {
    width: u32,
    /// The unsigned value, little-endian, unsigned, no sign byte.
    le_bytes: Vec<u8>,
}

impl BvValue {
    /// Builds a bit-vector value from a width and its little-endian magnitude.
    fn new(width: u32, le_bytes: Vec<u8>) -> Self {
        Self { width, le_bytes }
    }

    /// The value as a Python `int`.
    fn as_py_int<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        py.get_type::<PyInt>()
            .call_method1("from_bytes", (PyBytes::new(py, &self.le_bytes), "little"))
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl BvValue {
    /// The declared bit-vector width, in bits.
    #[getter]
    fn width(&self) -> u32 {
        self.width
    }

    /// The unsigned value as an arbitrary-precision Python integer.
    #[getter]
    fn value<'py>(&self, py: Python<'py>) -> PyResult<PyBigInt<'py>> {
        self.as_py_int(py).map(PyBigInt::new)
    }

    fn __int__<'py>(&self, py: Python<'py>) -> PyResult<PyBigInt<'py>> {
        self.as_py_int(py).map(PyBigInt::new)
    }

    fn __index__<'py>(&self, py: Python<'py>) -> PyResult<PyBigInt<'py>> {
        self.as_py_int(py).map(PyBigInt::new)
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let value = self.as_py_int(py)?;
        Ok(format!("BvValue(width={}, value={value})", self.width))
    }

    fn __eq__<'py>(&self, other: &Bound<'py, PyAny>) -> Bound<'py, PyAny> {
        let py = other.py();
        match other.cast::<BvValue>() {
            Ok(other) => {
                let other = other.get();
                PyBool::new(
                    py,
                    self.width == other.width && self.le_bytes == other.le_bytes,
                )
                .to_owned()
                .into_any()
            }
            // A bit-vector is not an integer: it carries a width. Deferring
            // rather than answering `False` lets the other operand decide.
            Err(_) => py.NotImplemented().into_bound(py),
        }
    }

    fn __hash__(&self, py: Python<'_>) -> PyResult<isize> {
        // Hash the (width, value) pair the way `__eq__` compares it, through
        // Python's own tuple hash so `hash` agrees with `==`.
        let value = self.as_py_int(py)?;
        (self.width, value).into_pyobject(py)?.hash()
    }
}

/// Converts an IR [`Value`] into the Python object plan 01 exposes.
///
/// # Errors
///
/// Propagates any Python error raised while building the object (allocation,
/// `int.from_bytes`, `fractions.Fraction`).
pub(crate) fn value_to_py<'py>(py: Python<'py>, value: &Value) -> PyResult<Bound<'py, PyAny>> {
    match value {
        Value::Bool(b) => Ok(PyBool::new(py, *b).to_owned().into_any()),
        Value::Bv { width, value } => Ok(BvValue::new(*width, u128_le_bytes(*value))
            .into_pyobject(py)?
            .into_any()),
        Value::WideBv(wide) => Ok(BvValue::new(wide.width(), wide_le_bytes(wide))
            .into_pyobject(py)?
            .into_any()),
        Value::Int(i) => Ok(i.into_pyobject(py)?.into_any()),
        Value::Real(r) => Ok(fraction(py, r.numerator(), r.denominator())?.into_bound()),
        Value::Seq(elements) => seq_to_py(py, elements),
        Value::Array(array) => Ok(ArrayValue::build(array).into_pyobject(py)?.into_any()),
        Value::GenericArray(array) => Ok(GenericArrayValue::build(py, array)?
            .into_pyobject(py)?
            .into_any()),
        Value::RealAlgebraic(number) => Ok(RealAlgebraicValue::build(number.clone())
            .into_pyobject(py)?
            .into_any()),
        Value::Datatype {
            datatype,
            constructor,
            fields,
        } => {
            let mut converted = Vec::with_capacity(fields.len());
            for field in fields {
                converted.push(value_to_py(py, field)?.unbind());
            }
            Ok(DatatypeValue {
                datatype: datatype.index(),
                constructor: constructor.index(),
                fields: PyTuple::new(py, converted)?.unbind(),
            }
            .into_pyobject(py)?
            .into_any())
        }
        Value::Uninterpreted { sort, value } => Ok(UninterpretedValue {
            sort: sort.index(),
            token: *value,
        }
        .into_pyobject(py)?
        .into_any()),
    }
}

/// A bit-vector-indexed array value: a default element plus its overrides.
///
/// Normalized by the IR (entries equal to the default are removed), so
/// equality here is extensional and the entry order is deterministic.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "ArrayValue")]
#[derive(Debug, Clone)]
pub struct ArrayValue {
    index_width: u32,
    element_width: u32,
    default: u128,
    entries: Vec<(u128, u128)>,
}

impl ArrayValue {
    fn build(array: &axeyum_ir::ArrayValue) -> Self {
        Self {
            index_width: array.index_width(),
            element_width: array.element_width(),
            default: array.default_element(),
            entries: array.entries().collect(),
        }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl ArrayValue {
    /// The index bit-vector width.
    #[getter]
    fn index_width(&self) -> u32 {
        self.index_width
    }

    /// The element bit-vector width.
    #[getter]
    fn element_width(&self) -> u32 {
        self.element_width
    }

    /// The element every un-overridden index maps to.
    #[getter]
    fn default<'py>(&self, py: Python<'py>) -> PyResult<PyBigInt<'py>> {
        BvValue::new(self.element_width, u128_le_bytes(self.default))
            .as_py_int(py)
            .map(PyBigInt::new)
    }

    /// The overriding `(index, element)` pairs, in index order.
    #[getter]
    fn entries<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyList>> {
        let list = PyList::empty(py);
        for (index, element) in &self.entries {
            let index = BvValue::new(self.index_width, u128_le_bytes(*index));
            let element = BvValue::new(self.element_width, u128_le_bytes(*element));
            list.append((index, element))?;
        }
        Ok(list)
    }

    /// The element at `index`, honoring the default.
    fn select(&self, index: u128) -> u128 {
        let index = if self.index_width >= 128 {
            index
        } else {
            index & ((1u128 << self.index_width) - 1)
        };
        self.entries
            .iter()
            .find(|(i, _)| *i == index)
            .map_or(self.default, |(_, element)| *element)
    }

    fn __len__(&self) -> usize {
        self.entries.len()
    }

    fn __repr__(&self) -> String {
        format!(
            "ArrayValue(index_width={}, element_width={}, default={}, entries={})",
            self.index_width,
            self.element_width,
            self.default,
            self.entries.len()
        )
    }
}

/// An array value over arbitrary (non-array) component sorts.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "GenericArrayValue"
)]
pub struct GenericArrayValue {
    index_sort: PySort,
    element_sort: PySort,
    default: Py<PyAny>,
    entries: Py<PyList>,
}

impl GenericArrayValue {
    fn build(py: Python<'_>, array: &axeyum_ir::GenericArrayValue) -> PyResult<Self> {
        let entries = PyList::empty(py);
        for (index, element) in array.entries() {
            entries.append((value_to_py(py, index)?, value_to_py(py, element)?))?;
        }
        Ok(Self {
            index_sort: PySort::universal(array.index_sort().to_sort()),
            element_sort: PySort::universal(array.element_sort().to_sort()),
            default: value_to_py(py, array.default_value())?.unbind(),
            entries: entries.unbind(),
        })
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl GenericArrayValue {
    /// The index sort.
    #[getter]
    fn index_sort(&self) -> PySort {
        self.index_sort
    }

    /// The element sort.
    #[getter]
    fn element_sort(&self) -> PySort {
        self.element_sort
    }

    /// The value every un-overridden index maps to.
    #[getter]
    fn default<'py>(&self, py: Python<'py>) -> Bound<'py, PyAny> {
        self.default.bind(py).clone()
    }

    /// The overriding `(index, element)` pairs.
    #[getter]
    fn entries<'py>(&self, py: Python<'py>) -> Bound<'py, PyList> {
        self.entries.bind(py).clone()
    }

    fn __len__(&self, py: Python<'_>) -> usize {
        self.entries.bind(py).len()
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!(
            "GenericArrayValue(index_sort={}, element_sort={}, entries={})",
            self.index_sort.sort,
            self.element_sort.sort,
            self.entries.bind(py).len()
        )
    }
}

/// A datatype value: which constructor built it, and its field values.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "DatatypeValue")]
pub struct DatatypeValue {
    datatype: usize,
    constructor: usize,
    fields: Py<PyTuple>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl DatatypeValue {
    /// The arena-local datatype index.
    #[getter]
    fn datatype(&self) -> usize {
        self.datatype
    }

    /// The arena-local constructor index.
    #[getter]
    fn constructor(&self) -> usize {
        self.constructor
    }

    /// The field values, in constructor-declaration order.
    #[getter]
    fn fields<'py>(&self, py: Python<'py>) -> Bound<'py, PyTuple> {
        self.fields.bind(py).clone()
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!(
            "DatatypeValue(datatype={}, constructor={}, fields={})",
            self.datatype,
            self.constructor,
            self.fields.bind(py).len()
        )
    }
}

/// A value of an uninterpreted carrier sort.
///
/// The token has no arithmetic meaning. Two values of the same declared sort
/// are equal exactly when their tokens are; nothing else about the number is
/// a claim the solver made.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "UninterpretedValue"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UninterpretedValue {
    sort: usize,
    token: u128,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl UninterpretedValue {
    /// The arena-local declared carrier sort index.
    #[getter]
    fn sort(&self) -> usize {
        self.sort
    }

    /// The equivalence-class token.
    #[getter]
    fn token(&self) -> u128 {
        self.token
    }

    fn __repr__(&self) -> String {
        format!(
            "UninterpretedValue(sort={}, token={})",
            self.sort, self.token
        )
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<Self>()
            .is_ok_and(|other| *self == *other.get())
    }

    fn __hash__(&self) -> u64 {
        // A hash may collide; truncating the token here is a collision, not a
        // wrong answer, and `__eq__` compares the full value.
        (self.sort as u64)
            .wrapping_mul(31)
            .wrapping_add(u64::try_from(self.token & u128::from(u64::MAX)).unwrap_or(0))
    }
}

/// A real algebraic number: the unique root of `defining_poly` inside
/// `interval`.
///
/// `sqrt(2)` is the root of `x^2 - 2` in `(1, 2)`. The IR supports sign and
/// comparison on this variant; field arithmetic is deferred (ADR-0038), so the
/// evaluator declines rather than returning a wrong value.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "RealAlgebraicValue"
)]
pub struct RealAlgebraicValue {
    number: axeyum_ir::RealAlgebraic,
}

impl RealAlgebraicValue {
    fn build(number: axeyum_ir::RealAlgebraic) -> Self {
        Self { number }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl RealAlgebraicValue {
    /// The defining integer polynomial, lowest-degree coefficient first.
    ///
    /// Arbitrary precision: the coefficients come across as Python `int`s
    /// through their decimal text, never truncated to a machine word.
    #[getter]
    fn defining_poly<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyList>> {
        let list = PyList::empty(py);
        for coefficient in self.number.defining_poly() {
            let text = coefficient.to_string();
            list.append(py.get_type::<PyInt>().call1((text, 10))?)?;
        }
        Ok(list)
    }

    /// The isolating interval as exact `Fraction`s, or `None` when its
    /// endpoints exceed the `i128` rational range.
    #[getter]
    fn interval<'py>(
        &self,
        py: Python<'py>,
    ) -> PyResult<Option<(PyFraction<'py>, PyFraction<'py>)>> {
        self.number
            .interval()
            .map(|(lo, hi)| {
                Ok((
                    fraction(py, lo.numerator(), lo.denominator())?,
                    fraction(py, hi.numerator(), hi.denominator())?,
                ))
            })
            .transpose()
    }

    /// The interval midpoint as an exact `Fraction`, when representable.
    ///
    /// An APPROXIMATION, not the value: an algebraic number is generally
    /// irrational and has no exact `Fraction`.
    #[getter]
    fn approx_midpoint<'py>(&self, py: Python<'py>) -> PyResult<Option<PyFraction<'py>>> {
        self.number
            .approx_midpoint()
            .map(|q| fraction(py, q.numerator(), q.denominator()))
            .transpose()
    }

    fn __repr__(&self) -> String {
        format!(
            "RealAlgebraicValue({})",
            Value::RealAlgebraic(self.number.clone())
        )
    }

    fn __str__(&self) -> String {
        Value::RealAlgebraic(self.number.clone()).to_string()
    }
}

/// A finite interpretation of an uninterpreted function.
///
/// `default` is the result for every argument tuple not in `entries`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "FuncValue")]
pub struct FuncValue {
    params: Vec<PySort>,
    result: PySort,
    default: Py<PyAny>,
    entries: Py<PyList>,
}

impl FuncValue {
    /// Copies a Rust function interpretation into Python objects.
    pub(crate) fn build(py: Python<'_>, func: &axeyum_ir::FuncValue) -> PyResult<Self> {
        let entries = PyList::empty(py);
        if func.uses_value_storage() {
            for (args, result) in func.value_entries() {
                let mut converted = Vec::with_capacity(args.len());
                for arg in args {
                    converted.push(value_to_py(py, arg)?);
                }
                entries.append((PyTuple::new(py, converted)?, value_to_py(py, result)?))?;
            }
        } else {
            let params = func.params().to_vec();
            for (args, result) in func.entries() {
                let mut converted = Vec::with_capacity(args.len());
                for (index, code) in args.iter().enumerate() {
                    let sort = params.get(index).copied().unwrap_or(Sort::Bool);
                    converted.push(value_to_py(py, &Value::from_scalar_code(sort, *code))?);
                }
                entries.append((
                    PyTuple::new(py, converted)?,
                    value_to_py(py, &Value::from_scalar_code(func.result(), result))?,
                ))?;
            }
        }
        Ok(Self {
            params: func
                .params()
                .iter()
                .map(|&sort| PySort::universal(sort))
                .collect(),
            result: PySort::universal(func.result()),
            default: value_to_py(py, &func.default_value())?.unbind(),
            entries: entries.unbind(),
        })
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl FuncValue {
    /// The parameter sorts.
    #[getter]
    fn params<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyList>> {
        // `PySort` is a `#[pyclass]`, so `&PySort` has no `IntoPyObject`; the
        // choice is a `Vec` clone or building the list straight from the
        // iterator. `PyList::new` over an `ExactSizeIterator` presizes the list
        // and fills it in place, so the intermediate `Vec` never exists.
        PyList::new(py, self.params.iter().copied())
    }

    /// The result sort.
    #[getter]
    fn result(&self) -> PySort {
        self.result
    }

    /// The result for every argument tuple not listed in `entries`.
    #[getter]
    fn default<'py>(&self, py: Python<'py>) -> Bound<'py, PyAny> {
        self.default.bind(py).clone()
    }

    /// The `(args tuple, result)` pairs the interpretation pins.
    #[getter]
    fn entries<'py>(&self, py: Python<'py>) -> Bound<'py, PyList> {
        self.entries.bind(py).clone()
    }

    fn __len__(&self, py: Python<'_>) -> usize {
        self.entries.bind(py).len()
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!(
            "FuncValue(arity={}, entries={})",
            self.params.len(),
            self.entries.bind(py).len()
        )
    }
}

/// Converts a Python object into an IR [`Value`] of `sort`.
///
/// The sort decides which Python type is accepted; nothing is guessed. This is
/// the inverse of [`value_to_py`] for the variants a caller can build.
///
/// # Errors
///
/// Raises `SortError` when the object cannot denote a value of `sort`.
pub(crate) fn py_to_value(object: &Bound<'_, PyAny>, sort: Sort) -> PyResult<Value> {
    match sort {
        Sort::Bool => {
            Ok(Value::Bool(object.extract::<bool>().map_err(|_| {
                SortError::new_err("Bool needs a Python bool")
            })?))
        }
        Sort::BitVec(width) => bv_from_py(object, width),
        Sort::Float { exp, sig } => bv_from_py(object, exp + sig),
        Sort::RoundingMode => bv_from_py(object, 3),
        Sort::Int => Ok(Value::Int(object.extract::<i128>().map_err(|_| {
            SortError::new_err("Int needs a Python int inside the i128 reference range")
        })?)),
        Sort::Real => {
            let numerator: i128 = object
                .getattr("numerator")
                .and_then(|n| n.extract())
                .map_err(|_| SortError::new_err("Real needs a fractions.Fraction (or an int)"))?;
            let denominator: i128 = object
                .getattr("denominator")
                .and_then(|d| d.extract())
                .map_err(|_| SortError::new_err("Real needs a fractions.Fraction (or an int)"))?;
            let rational = Rational::checked_new(numerator, denominator).ok_or_else(|| {
                SortError::new_err("rational is outside the i128 reference range")
            })?;
            Ok(Value::Real(rational))
        }
        Sort::Seq(ArraySortKey::BitVec(width)) => {
            let text: String = object
                .extract()
                .map_err(|_| SortError::new_err("a sequence of code points needs a Python str"))?;
            Ok(Value::Seq(
                text.chars()
                    .map(|c| Value::Bv {
                        width,
                        value: u128::from(u32::from(c)),
                    })
                    .collect(),
            ))
        }
        other => Err(SortError::new_err(format!(
            "no Python value can denote sort {other} yet; build it through the solver instead"
        ))),
    }
}

/// A bit-vector value of `width` from a Python `int` or [`BvValue`].
fn bv_from_py(object: &Bound<'_, PyAny>, width: u32) -> PyResult<Value> {
    if let Ok(existing) = object.cast::<BvValue>() {
        let existing = existing.get();
        if existing.width != width {
            return Err(SortError::new_err(format!(
                "BvValue is {} bits, the symbol is {width}",
                existing.width
            )));
        }
        let bits = le_bytes_to_lsb_bits(&existing.le_bytes, width);
        return axeyum_ir::lsb_bits_to_value(Sort::BitVec(width), &bits)
            .map_err(|error| SortError::new_err(error.to_string()));
    }
    let bits = crate::ir::arena::python_int_to_lsb_bits(object, width)?;
    axeyum_ir::lsb_bits_to_value(Sort::BitVec(width), &bits)
        .map_err(|error| SortError::new_err(error.to_string()))
}

/// LSB-first bits of a little-endian magnitude, at `width` bits.
fn le_bytes_to_lsb_bits(bytes: &[u8], width: u32) -> Vec<bool> {
    (0..width as usize)
        .map(|index| {
            bytes
                .get(index / 8)
                .is_some_and(|byte| byte & (1 << (index % 8)) != 0)
        })
        .collect()
}

/// The SMT-LIB `String`/`Seq` rendering: a sequence of scalar code points comes
/// back as a Python `str`.
///
/// A sequence whose elements are not all code points (a `(Seq Int)`, say) is a
/// Python `list` of converted elements instead — never a half-decoded string.
fn seq_to_py<'py>(py: Python<'py>, elements: &[Value]) -> PyResult<Bound<'py, PyAny>> {
    let mut text = String::with_capacity(elements.len());
    let mut is_text = true;
    for element in elements {
        if let Some(c) = code_point(element) {
            text.push(c);
        } else {
            is_text = false;
            break;
        }
    }
    if is_text {
        return Ok(PyString::new(py, &text).into_any());
    }
    let list = PyList::empty(py);
    for element in elements {
        list.append(value_to_py(py, element)?)?;
    }
    Ok(list.into_any())
}

/// The Unicode scalar a sequence element denotes, when it denotes one.
fn code_point(element: &Value) -> Option<char> {
    let Value::Bv { value, .. } = element else {
        return None;
    };
    u32::try_from(*value).ok().and_then(char::from_u32)
}

/// `fractions.Fraction(numerator, denominator)`.
fn fraction(py: Python<'_>, numerator: i128, denominator: i128) -> PyResult<PyFraction<'_>> {
    PyModule::import(py, "fractions")?
        .getattr("Fraction")?
        .call1((numerator, denominator))
        .map(PyFraction::new)
}

/// The little-endian magnitude of a `u128`, trailing zero bytes kept (they are
/// harmless to `int.from_bytes`).
fn u128_le_bytes(value: u128) -> Vec<u8> {
    value.to_le_bytes().to_vec()
}

/// The little-endian magnitude of a wide bit-vector, read out of its bits.
///
/// `WideUint` exposes `bit(i)` and `width()`; packing LSB-first is the only
/// representation-independent way to get its magnitude out.
fn wide_le_bytes(wide: &axeyum_ir::WideUint) -> Vec<u8> {
    let bits = wide.to_lsb_bits();
    let mut bytes = vec![0u8; bits.len().div_ceil(8)];
    for (i, bit) in bits.iter().enumerate() {
        if *bit {
            bytes[i / 8] |= 1 << (i % 8);
        }
    }
    bytes
}

/// Builds `{name: value}` for a list of named model entries, preserving the
/// caller's order (Python dicts are insertion-ordered, and the caller's order is
/// declaration order — determinism is a public API promise).
///
/// # Errors
///
/// Propagates any Python error raised while converting an entry.
pub(crate) fn model_dict<'py>(
    py: Python<'py>,
    entries: &[(String, Value)],
) -> PyResult<Bound<'py, PyDict>> {
    let dict = PyDict::new(py);
    for (name, value) in entries {
        dict.set_item(name, value_to_py(py, value)?)?;
    }
    Ok(dict)
}

/// Registers the conversion types on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<BvValue>()?;
    module.add_class::<ArrayValue>()?;
    module.add_class::<GenericArrayValue>()?;
    module.add_class::<DatatypeValue>()?;
    module.add_class::<UninterpretedValue>()?;
    module.add_class::<RealAlgebraicValue>()?;
    module.add_class::<FuncValue>()?;
    Ok(())
}
