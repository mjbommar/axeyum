//! `axeyum._native.cas.certify` — one submodule per certificate route.
//!
//! Each route ships the same shape, and the shape is the point:
//!
//! * a **producer** (`certify_*`, `reduce_*`, `zeilberger`, …) that is
//!   *untrusted* and returns a typed outcome, never a bool;
//! * a **certificate** that carries every distinction its producer made, so an
//!   independent checker can re-derive the refutation;
//! * a **checker** returning a verdict **with its report counts**. A zero count
//!   is the fail signal, and a checker whose exit cannot depend on what it found
//!   is worse than no checker at all.

pub(crate) mod ansatz;
pub(crate) mod geometry;
pub(crate) mod gf2;
pub(crate) mod groebner;
pub(crate) mod moments;
pub(crate) mod sos;
pub(crate) mod sturm;
pub(crate) mod telescoping;

use pyo3::prelude::*;
use pyo3::types::PyModule;

/// The route submodules, in registration order. Used to populate `sys.modules`.
pub(crate) const ROUTES: &[&str] = &[
    "ansatz",
    "geometry",
    "gf2",
    "groebner",
    "moments",
    "sos",
    "sturm",
    "telescoping",
];

/// Registers the `certify` submodule on `parent` and returns it.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.cas.certify")?;
    ansatz::register(&module)?;
    geometry::register(&module)?;
    gf2::register(&module)?;
    moments::register(&module)?;
    groebner::register(&module)?;
    sos::register(&module)?;
    sturm::register(&module)?;
    telescoping::register(&module)?;
    parent.add("certify", &module)?;
    Ok(module)
}
