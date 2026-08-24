//! Conversion of Axeyum IR values into Python objects.
//!
//! The rule is *sound, never inventive*: a variant is mapped to a Python type
//! only when the mapping is total and loses nothing. Everything else is handed
//! over as its `Display` rendering — readable, obviously not a number, and
//! impossible to mistake for a structured value.

use axeyum_ir::Value;
use pyo3::prelude::*;
use pyo3::types::{PyBool, PyBytes, PyDict, PyInt, PyList, PyModule, PyString};

/// A bit-vector value: an unsigned integer together with the width it was
/// produced at.
///
/// The width is the part a plain Python `int` cannot carry, and it is exactly
/// what a caller needs to re-form the value as an SMT-LIB literal. The integer
/// itself is arbitrary-precision on the Python side, so `Value::Bv` (width
/// <= 128) and `Value::WideBv` (width > 128) converge on this one type — the
/// split in the Rust IR is a storage detail, not a semantic one.
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

#[pymethods]
impl BvValue {
    /// The declared bit-vector width, in bits.
    #[getter]
    fn width(&self) -> u32 {
        self.width
    }

    /// The unsigned value as an arbitrary-precision Python integer.
    #[getter]
    fn value<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.as_py_int(py)
    }

    fn __int__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.as_py_int(py)
    }

    fn __index__<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.as_py_int(py)
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
        Value::Real(r) => fraction(py, r.numerator(), r.denominator()),
        Value::Seq(elements) => seq_to_py(py, elements),
        // TODO(plan 02): real-algebraic values (defining polynomial + isolating
        // interval), array/datatype/uninterpreted values, and function
        // interpretations all need structured Python types. Rendering them is
        // sound and useless-but-honest; inventing a lossy `int` for them would
        // not be.
        Value::RealAlgebraic(_)
        | Value::Array(_)
        | Value::GenericArray(_)
        | Value::Datatype { .. }
        | Value::Uninterpreted { .. } => Ok(PyString::new(py, &value.to_string()).into_any()),
    }
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
fn fraction(py: Python<'_>, numerator: i128, denominator: i128) -> PyResult<Bound<'_, PyAny>> {
    PyModule::import(py, "fractions")?
        .getattr("Fraction")?
        .call1((numerator, denominator))
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
    Ok(())
}
