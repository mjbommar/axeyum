//! `axeyum.ir` (tier R + C) — sorts, terms, values, and the trusted evaluator.
//!
//! This is where a Python caller builds a query without going through SMT-LIB
//! text. Everything is a projection of `axeyum-ir`, `axeyum-bv`, `axeyum-fp`
//! and `axeyum-query`; nothing here decides anything.
//!
//! Three invariants cross the language boundary verbatim:
//!
//! * **Handles are epoch-checked.** A `Term` from arena A used against arena B
//!   raises `EpochError`. Rust would index out of range and panic.
//! * **Degenerate operators are total** with SMT-LIB semantics — `bvudiv x 0`
//!   is all-ones, `int_div a 0` is `0`, `int_mod a 0` is `a`. Nothing here
//!   raises `ZeroDivisionError`, and a caller expecting one will misread a
//!   correct answer.
//! * **`None` is a value.** The floating-point constant folders return `None`
//!   for "the argument was not constant"; that is neither an error nor `False`.

pub(crate) mod arena;
pub(crate) mod bits;
pub(crate) mod evaluate;
pub(crate) mod floats;
pub(crate) mod lowering;
pub(crate) mod query;
pub(crate) mod types;

use pyo3::prelude::*;
use pyo3::types::PyModule;

/// Builds the `ir` submodule.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.ir")?;
    module.add(
        "__doc__",
        "tier R + C -- sorts, terms, values, the trusted ground evaluator, bit \
         lowering, the floating-point builders and the query planner. Handles are \
         epoch-checked; degenerate operators are total with SMT-LIB semantics.",
    )?;
    module.add_class::<arena::Arena>()?;
    module.add_class::<types::Term>()?;
    module.add_class::<types::Symbol>()?;
    module.add_class::<types::Func>()?;
    module.add_class::<types::SortRef>()?;
    module.add_class::<types::Datatype>()?;
    module.add_class::<types::Constructor>()?;
    module.add_class::<types::PySort>()?;
    module.add_class::<types::PyTermNode>()?;
    module.add_class::<types::PyTermStats>()?;
    module.add("EpochError", py.get_type::<types::EpochError>())?;
    module.add("SortError", py.get_type::<types::SortError>())?;
    module.add("MAX_BV_WIDTH", axeyum_ir::MAX_BV_WIDTH)?;
    module.add("STRING_ELEM_WIDTH", axeyum_ir::Sort::STRING_ELEM_WIDTH)?;
    module.add("OP_NAMES", types::all_op_names(py)?)?;
    evaluate::register(&module)?;

    let sys_modules = py.import("sys")?.getattr("modules")?;
    for (name, submodule) in [
        ("bits", bits::register(&module)?),
        ("bv", lowering::register(&module)?),
        ("fp", floats::register(&module)?),
        ("query", query::register(&module)?),
    ] {
        sys_modules.set_item(format!("axeyum._native.ir.{name}"), &submodule)?;
    }
    parent.add("ir", &module)?;
    Ok(module)
}

// Module-level constants reach Python through `module.add("NAME", value)`, a
// RUNTIME call with no item for a `#[gen_stub_*]` macro to sit on -- so without
// these submissions they exist in the extension and in no stub, and a checked
// consumer reading one gets an unresolved attribute. The type is named; the
// VALUE deliberately is not, so a constant cannot drift from its stub.
#[cfg(feature = "stub-gen")]
mod stub_variables {
    pyo3_stub_gen::module_variable!("axeyum._native.ir", "MAX_BV_WIDTH", u32);
    pyo3_stub_gen::module_variable!("axeyum._native.ir", "STRING_ELEM_WIDTH", u32);
    pyo3_stub_gen::module_variable!(
        "axeyum._native.ir",
        "OP_NAMES",
        crate::stub_types::PyFrozenSetOf<String>
    );
}
