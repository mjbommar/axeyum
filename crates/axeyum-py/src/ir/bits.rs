//! `axeyum.ir.bits` — the LSB-first bit conversions.
//!
//! **LSB-first is the project-wide convention.** Index `0` is the least
//! significant bit in every list this module produces or consumes, and in the
//! circuit-level vectors of [`ir.bv`](axeyum.ir.bv). Reversing one of these
//! lists silently produces a different bit-vector, not an error.
#![allow(clippy::needless_pass_by_value)]

use axeyum_ir::Sort;
use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::convert::{py_to_value, value_to_py};
use crate::ir::types::{PySort, map_ir_error};

/// The LSB-first bits of a bit-vector of `width` bits.
#[pyfunction]
pub fn bv_value_to_lsb_bits(width: u32, value: &Bound<'_, PyAny>) -> PyResult<Vec<bool>> {
    crate::ir::arena::python_int_to_lsb_bits(value, width)
}

/// The bit-vector value LSB-first `bits` denote.
#[pyfunction]
pub fn lsb_bits_to_bv_value(py: Python<'_>, bits: Vec<bool>) -> PyResult<Bound<'_, PyAny>> {
    let value = axeyum_ir::lsb_bits_to_bv_value(&bits).map_err(|error| map_ir_error(&error))?;
    value_to_py(py, &value)
}

/// The value of `sort` that LSB-first `bits` denote.
///
/// Raises `SortError` when the bit count does not match the sort's lowered
/// width — a length mismatch is never silently padded or truncated.
#[pyfunction]
pub fn lsb_bits_to_value<'py>(
    py: Python<'py>,
    sort: &PySort,
    bits: Vec<bool>,
) -> PyResult<Bound<'py, PyAny>> {
    let sort: Sort = sort.sort;
    let value = axeyum_ir::lsb_bits_to_value(sort, &bits).map_err(|error| map_ir_error(&error))?;
    value_to_py(py, &value)
}

/// The LSB-first bits of a scalar Python value of `sort`.
#[pyfunction]
pub fn value_to_lsb_bits(sort: &PySort, value: &Bound<'_, PyAny>) -> PyResult<Vec<bool>> {
    let value = py_to_value(value, sort.sort)?;
    axeyum_ir::value_to_lsb_bits(value).map_err(|error| map_ir_error(&error))
}

/// Builds the `ir.bits` submodule.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.ir.bits")?;
    module.add("__doc__", "tier R -- LSB-first bit conversions.")?;
    module.add_function(wrap_pyfunction!(bv_value_to_lsb_bits, &module)?)?;
    module.add_function(wrap_pyfunction!(lsb_bits_to_bv_value, &module)?)?;
    module.add_function(wrap_pyfunction!(lsb_bits_to_value, &module)?)?;
    module.add_function(wrap_pyfunction!(value_to_lsb_bits, &module)?)?;
    module.add("LSB_FIRST", true)?;
    parent.add("bits", &module)?;
    Ok(module)
}
