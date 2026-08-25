//! `axeyum._native.cas` — the computer-algebra surface, and `cas.certify`, its
//! producer/checker pairs.
//!
//! Two rules from the Rust side cross unchanged:
//!
//! * **`None` is a value.** Across this crate `Option::None` means *outside the
//!   fragment, declined, or `i128` overflow* — never an error. Nothing here maps
//!   it to an exception.
//! * **A checker returns a report, not a bool.** Every `check()` in
//!   [`certify`] hands back the verdict *with its counts*, because a checker
//!   whose result cannot be falsified is worse than no checker at all.

// Five pedantic lints are relaxed for this whole module tree because `PyO3`
// dictates the signatures they object to, not the code: a `#[pymethods]`
// function takes `&self` even when the receiver is a one-byte `Copy` tag
// (`trivially_copy_pass_by_ref`, `unused_self`, `wrong_self_convention`); a
// `#[pyfunction]` extracts an owned `Vec<T>` because there is no borrowed form
// to extract into (`needless_pass_by_value`); and a checker that returns its
// counts alongside its answer has a genuinely wide return type
// (`type_complexity`) -- flattening it would mean dropping a count, which is
// the one thing this surface must not do.
#![allow(
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref,
    clippy::type_complexity,
    clippy::unused_self,
    clippy::wrong_self_convention
)]

pub(crate) mod algebraic;
pub(crate) mod boolean;
pub(crate) mod certify;
pub(crate) mod combinatorics;
pub(crate) mod expr;
pub(crate) mod functions;
pub(crate) mod gf;
pub(crate) mod normal_forms;
pub(crate) mod ntheory;
pub(crate) mod poly;
pub(crate) mod rational;
pub(crate) mod special;
pub(crate) mod stats;
pub(crate) mod transforms;

use pyo3::create_exception;
use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::error::AxeyumError;

create_exception!(
    axeyum,
    CasError,
    AxeyumError,
    "A CAS artifact was malformed, or a checker discharged no obligation.\n\nThis is NOT how an undecided computation surfaces: `normalize`, `factor`,\n`integrate` and friends return `None` for *declined or overflowed*, which is a\nvalue, not an error."
);
create_exception!(
    axeyum,
    Gf2Error,
    CasError,
    "A GF(2) budget, shape, or certificate-structure refusal.\n\nA *reducible* polynomial is not this: `certify_irreducible` returns `None`\nfor it, which is a decided answer."
);

/// Registers the `cas` submodule on `parent` and returns it.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    // The FULL dotted name, so `repr(axeyum.cas)` and every traceback name the
    // module the way an import statement spells it.
    let module = PyModule::new(py, "axeyum._native.cas")?;

    module.add("CasError", py.get_type::<CasError>())?;
    module.add("Gf2Error", py.get_type::<Gf2Error>())?;

    module.add_class::<rational::Rational>()?;
    module.add_class::<expr::Expr>()?;
    module.add_class::<expr::ZeroTest>()?;
    module.add_class::<expr::Certainty>()?;
    module.add_class::<expr::Sign>()?;
    module.add_class::<expr::CertifiedIntegral>()?;
    module.add_class::<expr::DefiniteIntegral>()?;
    module.add_class::<expr::LimitPoint>()?;
    module.add_class::<expr::Assumptions>()?;
    module.add_class::<poly::Monomial>()?;
    module.add_class::<poly::MvPoly>()?;
    module.add_class::<poly::MultiPoly>()?;
    functions::register(&module)?;
    ntheory::register(&module)?;
    combinatorics::register(&module)?;
    stats::register(&module)?;
    special::register(&module)?;
    transforms::register(&module)?;
    normal_forms::register(&module)?;
    algebraic::register(&module)?;
    gf::register(&module)?;
    boolean::register(&module)?;

    // `add_submodule` sets the attribute but not `sys.modules`, so without this
    // `import axeyum._native.cas.certify` fails while the attribute resolves --
    // the split plan 01 already paid for once.
    let certify_module = certify::register(&module)?;
    let sys_modules = py.import("sys")?.getattr("modules")?;
    sys_modules.set_item("axeyum._native.cas.certify", &certify_module)?;
    for name in certify::ROUTES {
        let route = certify_module.getattr(*name)?;
        sys_modules.set_item(format!("axeyum._native.cas.certify.{name}"), route)?;
    }

    parent.add("cas", &module)?;
    Ok(module)
}

// See `crate::error`: an exception is a `PyErr` type, not a `#[pyclass]`, so the
// stub record has to be submitted separately.
#[cfg(feature = "stub-gen")]
mod stub {
    use super::{CasError, Gf2Error};
    use crate::error::AxeyumError;
    use crate::stub_info::stub_exception;

    stub_exception!(
        "axeyum._native.cas",
        CasError,
        AxeyumError,
        "A CAS artifact was malformed, or a checker discharged no obligation."
    );
    stub_exception!(
        "axeyum._native.cas",
        Gf2Error,
        CasError,
        "A GF(2) budget, shape, or certificate-structure refusal."
    );
}
