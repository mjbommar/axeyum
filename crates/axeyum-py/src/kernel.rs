//! `axeyum._native.kernel` — registration stub; filled by plan 02.

use pyo3::prelude::*;

/// Registers the `kernel` submodule on `parent` and returns it.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let module = PyModule::new(parent.py(), "kernel")?;
    parent.add_submodule(&module)?;
    Ok(module)
}
