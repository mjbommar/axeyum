//! `axeyum.machine` — executable instruction-set teaching semantics.
//!
//! This module projects the Rust types from `axeyum-machine`. Python selects
//! examples and displays results; it does not reimplement word, decoder, state,
//! or transition meaning.

pub(crate) mod a0;
pub(crate) mod rv64;
pub(crate) mod x64;

use pyo3::prelude::*;
use pyo3::types::PyModule;

/// Registers the executable-machine module and its architecture submodules.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating a module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.machine")?;
    module.add(
        "__doc__",
        "tier R -- executable instruction-set teaching semantics projected from Rust.",
    )?;
    let a0_module = a0::register(&module)?;
    let rv64_module = rv64::register(&module)?;
    let x64_module = x64::register(&module)?;
    let sys_modules = py.import("sys")?.getattr("modules")?;
    sys_modules.set_item("axeyum._native.machine.a0", &a0_module)?;
    sys_modules.set_item("axeyum._native.machine.rv64", &rv64_module)?;
    sys_modules.set_item("axeyum._native.machine.x64", &x64_module)?;
    parent.add("machine", &module)?;
    Ok(module)
}
