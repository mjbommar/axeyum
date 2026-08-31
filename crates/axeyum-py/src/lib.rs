//! Python bindings for the Axeyum automated reasoning stack.
//!
//! The extension module is imported as `axeyum._native`; the pure-Python
//! package under `python/axeyum/` re-exports its surface.
//!
//! # What this crate is allowed to be
//!
//! **A projection of the Rust API.** No function exists here that does not
//! exist in Rust, and no call through it can admit a fact, write a ledger,
//! relax a checker, or change an axiom footprint — because the Rust API it
//! wraps has no such route to expose. `unknown` and `declined` cross the
//! language boundary as *values*, exactly as they do in Rust.
//!
//! # Build note
//!
//! `pyo3/extension-module` is **not** a default Cargo feature of this crate.
//! With it on, `cargo test --workspace` fails to link (a cdylib cannot resolve
//! the Python symbols); maturin supplies it through `[tool.maturin] features`
//! in the root `pyproject.toml`.

mod cas;
mod convert;
mod error;
mod ir;
mod kernel;
mod machine;
mod producers;
mod smt;
mod solver;
#[cfg(feature = "stub-gen")]
mod stub_info;
mod stub_types;

#[cfg(feature = "stub-gen")]
pub use stub_info::stub_info;

use pyo3::prelude::*;
use pyo3::types::PyModule;

/// The Axeyum workspace version this extension module was built from.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native")
)]
#[pyfunction]
fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

/// The `axeyum._native` extension module.
///
/// `gil_used = true` is deliberate and honest: `PyO3` 0.28+ defaults to
/// *declaring* the module thread-safe, and the `Sync` audit of this crate's
/// mutable state has not been done. It costs a `RuntimeWarning` on
/// free-threaded builds only, which the abi3 wheel does not target.
///
/// # Errors
///
/// Propagates any Python error raised while registering the submodules.
#[pymodule(gil_used = true)]
fn _native(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_function(wrap_pyfunction!(version, module)?)?;
    module.add("__version__", version())?;
    error::register(module)?;
    convert::register(module)?;
    // `add_submodule` sets the attribute but not `sys.modules`, so without this
    // `import axeyum._native.smt` fails while `axeyum._native.smt` works — a
    // split that surprises every consumer exactly once. One entry per
    // submodule; each submodule lives in its own file and registers itself.
    let py = module.py();
    let sys_modules = py.import("sys")?.getattr("modules")?;
    for (name, submodule) in [
        ("smt", smt::register(module)?),
        ("ir", ir::register(module)?),
        ("solver", solver::register(module)?),
        ("cas", cas::register(module)?),
        ("kernel", kernel::register(module)?),
        ("machine", machine::register(module)?),
        ("producers", producers::register(module)?),
    ] {
        sys_modules.set_item(format!("axeyum._native.{name}"), &submodule)?;
    }
    Ok(())
}

// Module-level constants reach Python through `module.add("NAME", value)`, a
// RUNTIME call with no item for a `#[gen_stub_*]` macro to sit on -- so without
// these submissions they exist in the extension and in no stub, and a checked
// consumer reading one gets an unresolved attribute. The type is named; the
// VALUE deliberately is not, so a constant cannot drift from its stub.
#[cfg(feature = "stub-gen")]
mod stub_variables {
    pyo3_stub_gen::module_variable!("axeyum._native", "__version__", String);
}
