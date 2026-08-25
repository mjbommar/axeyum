//! `axeyum.solver` (tier P + C) — decide, and then check what was decided.
//!
//! Two rules carried across the language boundary verbatim:
//!
//! * **`unknown` is a value.** A budget-exhausted or incomplete run returns a
//!   [`CheckResult`](axeyum.solver.CheckResult) with `status == "unknown"` and
//!   a classified `unknown_kind`; nothing here raises for it.
//! * **A checker that cannot fail is worse than no checker.** So
//!   `Evidence.check_outcome()` is bound and the `bool`-returning `check()` is
//!   not, `UnsatProof.recheck_lrat()` returns `None` rather than `True` when
//!   there is no LRAT, `check_drat` has a third answer for a budget miss, and
//!   `UnsatProofOutcome.Inconclusive` is not a pass.

pub(crate) mod cnf;
pub(crate) mod core;
pub(crate) mod ledgers;
pub(crate) mod proofs;
pub(crate) mod results;

use pyo3::prelude::*;
use pyo3::types::PyModule;

/// Builds the `solver` submodule.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.solver")?;
    module.add(
        "__doc__",
        "tier P + C -- decide term lists, produce checkable evidence, and re-derive \
         certificates. `unknown` is a value; every checker here can fail.",
    )?;
    module.add_class::<results::Config>()?;
    core::register(&module)?;
    ledgers::register(&module)?;
    module.add("UNKNOWN_KINDS", results::UNKNOWN_KINDS.to_vec())?;
    module.add(
        "STRATEGIES",
        vec!["eager_pure_rust", "lazy_bv_abstraction", "auto"],
    )?;

    let sys_modules = py.import("sys")?.getattr("modules")?;
    for (name, submodule) in [
        ("proofs", proofs::register(&module)?),
        ("cnf", cnf::register(&module)?),
    ] {
        sys_modules.set_item(format!("axeyum._native.solver.{name}"), &submodule)?;
    }
    parent.add("solver", &module)?;
    Ok(module)
}

// Module-level constants reach Python through `module.add("NAME", value)`, a
// RUNTIME call with no item for a `#[gen_stub_*]` macro to sit on -- so without
// these submissions they exist in the extension and in no stub, and a checked
// consumer reading one gets an unresolved attribute. The type is named; the
// VALUE deliberately is not, so a constant cannot drift from its stub.
#[cfg(feature = "stub-gen")]
mod stub_variables {
    pyo3_stub_gen::module_variable!("axeyum._native.solver", "UNKNOWN_KINDS", Vec<String>);
    pyo3_stub_gen::module_variable!("axeyum._native.solver", "STRATEGIES", Vec<String>);
}
