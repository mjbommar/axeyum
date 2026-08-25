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

create_exception!(
    axeyum,
    InternalError,
    AxeyumError,
    "A Rust invariant broke where the binding could not screen for it first.\n\nRaised INSTEAD of letting a `panic!` reach Python as\n`pyo3_runtime.PanicException`, which derives from `BaseException` and so\nescapes `except Exception`. The message names the Rust site. This is always\na bug in Axeyum, never a usage error: a usage error gets a specific type\n(`SortError`, `EpochError`, `ValueError`, `OverflowError`) from a preflight\ncheck. It exists only where a preflight is impossible -- see\n`docs/python-2026-08/13-panic-surface.md` for the rule and the list."
);

create_exception!(
    axeyum,
    ReplayUnavailable,
    AxeyumError,
    "`Outcome.replay()` was asked to re-check a model it does not hold.\n\nRaised for a non-`sat` outcome (there is no model to check) and for the one\nknown front-door route that decides `sat` without leaving a replayable\narena (a quantified query). It is deliberately NOT `False`: `False` means\n\"replayed and the model does not satisfy the assertions\" -- a soundness\nsignal -- and the two must never share a value."
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
    module.add("ReplayUnavailable", py.get_type::<ReplayUnavailable>())?;
    module.add("InternalError", py.get_type::<InternalError>())?;
    Ok(())
}

// The stub-inventory twin of the `create_exception!` calls above. `PyO3` builds
// an exception as a `PyErr` type rather than a `#[pyclass]`, so nothing a
// `#[gen_stub_*]` macro can be attached to exists -- without this the four names
// are absent from the generated stubs and every `except axeyum.AxeyumError` in a
// checked consumer is an unresolved attribute.
#[cfg(feature = "stub-gen")]
mod stub {
    use super::{AxeyumError, BudgetExceeded, InternalError, ReplayUnavailable, SmtLibParseError};
    use crate::stub_info::stub_exception;
    use pyo3::exceptions::PyException;

    stub_exception!(
        "axeyum._native",
        AxeyumError,
        PyException,
        "Root of every exception raised by the Axeyum bindings."
    );
    stub_exception!(
        "axeyum._native",
        SmtLibParseError,
        AxeyumError,
        "The SMT-LIB text could not be parsed, or used a construct outside the supported fragment."
    );
    stub_exception!(
        "axeyum._native",
        BudgetExceeded,
        AxeyumError,
        "A binding-level budget refused the call before any search started."
    );
    stub_exception!(
        "axeyum._native",
        ReplayUnavailable,
        AxeyumError,
        "`Outcome.replay()` was asked to re-check a model it does not hold."
    );
    stub_exception!(
        "axeyum._native",
        InternalError,
        AxeyumError,
        "A Rust invariant was violated inside a call that could not be guarded by a preflight; the message names the Rust site. Not a normal outcome -- report it."
    );
}
