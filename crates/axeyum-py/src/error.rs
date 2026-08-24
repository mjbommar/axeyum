//! The Python exception hierarchy for the Axeyum bindings.
//!
//! One root, `AxeyumError`, so a caller can catch everything this extension
//! raises with a single `except`. The two leaves below it are the only failure
//! modes plan 01's surface can produce.
//!
//! **`unknown` and `declined` are values, never exceptions** (CLAUDE.md hard
//! rule, carried verbatim across the language boundary). An undecided query
//! comes back as `Outcome(status="unknown", ...)`; nothing here is raised for
//! it, and `BudgetExceeded` exists for *binding-level* budget refusals, not for
//! a solver that ran out of time.

use pyo3::create_exception;
use pyo3::exceptions::PyException;
use pyo3::prelude::*;

// The macro stringifies its first token into the exception's `__module__`, so a
// dotted path is not expressible here. `axeyum` is the right answer anyway:
// `python/axeyum/__init__.py` re-exports every name below, so
// `axeyum.AxeyumError` resolves.
create_exception!(
    axeyum,
    AxeyumError,
    PyException,
    "Root of every exception raised by the Axeyum bindings."
);
create_exception!(
    axeyum,
    SmtLibParseError,
    AxeyumError,
    "The SMT-LIB text could not be parsed, or used a construct outside the supported fragment."
);
create_exception!(
    axeyum,
    BudgetExceeded,
    AxeyumError,
    "A binding-level budget refused the call before any search started.\n\nThis is NOT how a solver timeout surfaces: an exhausted solver budget is a\n`Outcome` with `status == \"unknown\"`, because `unknown` is a value."
);

/// Registers the exception types on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    let py = module.py();
    module.add("AxeyumError", py.get_type::<AxeyumError>())?;
    module.add("SmtLibParseError", py.get_type::<SmtLibParseError>())?;
    module.add("BudgetExceeded", py.get_type::<BudgetExceeded>())?;
    Ok(())
}
