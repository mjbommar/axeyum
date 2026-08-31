//! Python projection of the executable A0 teaching machine.

// PyO3 extracts an owned `Vec<u8>` for a Python sequence, and `Result::map_err`
// consumes the Rust error before it becomes a Python exception.
#![allow(clippy::needless_pass_by_value)]

use axeyum_machine::a0;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyModule};

fn value_error(error: a0::A0Error) -> PyErr {
    PyValueError::new_err(error.to_string())
}

/// A fixed-width A0 word with arithmetic values reduced modulo `2**width`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.machine.a0")
)]
#[pyclass(
    frozen,
    eq,
    skip_from_py_object,
    module = "axeyum.machine.a0",
    name = "Word"
)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Word {
    inner: a0::Word,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Word {
    /// Construct a word, reducing `value` modulo `2**width`.
    #[new]
    fn new(width: u8, value: u64) -> PyResult<Self> {
        Ok(Self {
            inner: a0::Word::new(width, value).map_err(value_error)?,
        })
    }

    /// Construct a word by joining least-significant byte first.
    #[staticmethod]
    fn from_little_endian(bytes: Vec<u8>) -> PyResult<Self> {
        Ok(Self {
            inner: a0::Word::from_little_endian(&bytes).map_err(value_error)?,
        })
    }

    /// Width in bits.
    #[getter]
    fn width(&self) -> u8 {
        self.inner.width()
    }

    /// Unsigned reading of the stored bit pattern.
    #[getter]
    fn unsigned(&self) -> u64 {
        self.inner.unsigned()
    }

    /// Signed two's-complement reading of the stored bit pattern.
    #[getter]
    fn signed(&self) -> i128 {
        self.inner.signed()
    }

    /// Whether the most-significant bit is one.
    #[getter]
    fn high_bit(&self) -> bool {
        self.inner.high_bit()
    }

    /// Bytes from least significant to most significant.
    fn little_endian_bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.little_endian_bytes())
    }

    /// Return the same pattern widened with zero high bits.
    fn zero_extend(&self, new_width: u8) -> PyResult<Self> {
        Ok(Self {
            inner: self.inner.zero_extend(new_width).map_err(value_error)?,
        })
    }

    /// Return the same signed value widened by repeating the sign bit.
    fn sign_extend(&self, new_width: u8) -> PyResult<Self> {
        Ok(Self {
            inner: self.inner.sign_extend(new_width).map_err(value_error)?,
        })
    }

    /// Keep only the least-significant `new_width` bits.
    fn truncate(&self, new_width: u8) -> PyResult<Self> {
        Ok(Self {
            inner: self.inner.truncate(new_width).map_err(value_error)?,
        })
    }

    fn __repr__(&self) -> String {
        format!("Word(width={}, value={:#x})", self.width(), self.unsigned())
    }

    fn __int__(&self) -> u64 {
        self.unsigned()
    }
}

/// Registers `axeyum.machine.a0`.
///
/// # Errors
///
/// Propagates any Python error raised while populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.machine.a0")?;
    module.add(
        "__doc__",
        "tier R -- executable A0 words, states, instructions, and traces projected from Rust.",
    )?;
    module.add_class::<Word>()?;
    parent.add("a0", &module)?;
    Ok(module)
}
