//! The trusted ground evaluator and its assignment.
//!
//! `axeyum_ir::eval` is the checker every `sat` result in this repository is
//! replayed against. It is bound here directly: nothing in the Python layer
//! re-implements it.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use axeyum_ir::{Assignment, Rational, Sort, Value};
use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::convert::{py_to_value, value_to_py};
use crate::ir::arena::Arena;
use crate::ir::types::{Symbol, Term, check_epoch, map_ir_error};

/// A partial map from declared symbols to concrete values.
///
/// Bound to one [`Arena`](axeyum.ir.Arena): every method takes the arena so the
/// binding can both check the epoch and coerce a Python value to the symbol's
/// declared sort.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir")
)]
#[pyclass(module = "axeyum", name = "Assignment")]
pub struct PyAssignment {
    pub(crate) assignment: Assignment,
    pub(crate) epoch: u64,
}

impl PyAssignment {
    pub(crate) fn empty(epoch: u64) -> Self {
        Self {
            assignment: Assignment::new(),
            epoch,
        }
    }

    pub(crate) fn wrap(epoch: u64, assignment: Assignment) -> Self {
        Self { assignment, epoch }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyAssignment {
    /// Creates an empty assignment bound to `arena`.
    #[new]
    fn new(arena: PyRef<'_, Arena>) -> Self {
        Self::empty(arena.epoch)
    }

    /// The arena epoch this assignment is bound to.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Binds `symbol` to `value`, coerced to the symbol's declared sort.
    ///
    /// `bool`, `int`, `BvValue`, `fractions.Fraction` and `str` are accepted;
    /// which of them fits is decided by the declared sort, never guessed.
    fn set(
        &mut self,
        arena: PyRef<'_, Arena>,
        symbol: Symbol,
        value: &Bound<'_, PyAny>,
    ) -> PyResult<()> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let symbol = symbol.resolve(self.epoch)?;
        let (_name, sort) = arena.arena.symbol(symbol);
        self.assignment.set(symbol, py_to_value(value, sort)?);
        Ok(())
    }

    /// The value bound to `symbol`, or `None`.
    fn get<'py>(&self, py: Python<'py>, symbol: Symbol) -> PyResult<Option<Bound<'py, PyAny>>> {
        let symbol = symbol.resolve(self.epoch)?;
        self.assignment
            .get(symbol)
            .map(|value| value_to_py(py, &value))
            .transpose()
    }

    /// Pins the value the evaluator uses for `numerator / 0`.
    fn set_real_div_zero(
        &mut self,
        numerator: (i128, i128),
        quotient: (i128, i128),
    ) -> PyResult<()> {
        let numerator = Rational::checked_new(numerator.0, numerator.1)
            .ok_or_else(|| crate::error::AxeyumError::new_err("numerator is not representable"))?;
        let quotient = Rational::checked_new(quotient.0, quotient.1)
            .ok_or_else(|| crate::error::AxeyumError::new_err("quotient is not representable"))?;
        self.assignment.set_real_div_zero(numerator, quotient);
        Ok(())
    }

    /// Number of bound symbols.
    fn __len__(&self) -> usize {
        self.assignment.len()
    }

    fn __repr__(&self) -> String {
        format!(
            "Assignment(epoch={}, bound={})",
            self.epoch,
            self.assignment.len()
        )
    }
}

/// Evaluates `term` under `assignment` — the trusted ground evaluator.
///
/// This is the checker, not a solver: it is total on ground terms whose
/// symbols are all bound, and it reports an error rather than a wrong value
/// when a result leaves the `i128` reference range.
///
/// SMT-LIB totality holds here verbatim, so `eval` of `(bvudiv x 0)` is
/// all-ones and `eval` of `(div a 0)` is `0` — no `ZeroDivisionError` is
/// raised for either.
///
/// # Errors
///
/// Raises `SortError` for an unbound symbol, an un-enumerable quantifier
/// domain, or an arithmetic overflow.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.ir")
)]
#[pyfunction]
pub fn eval<'py>(
    py: Python<'py>,
    arena: PyRef<'_, Arena>,
    term: Term,
    assignment: PyRef<'_, PyAssignment>,
) -> PyResult<Bound<'py, PyAny>> {
    check_epoch(arena.epoch, assignment.epoch, "Assignment")?;
    let id = term.resolve(arena.epoch)?;
    let value = axeyum_ir::eval(&arena.arena, id, &assignment.assignment)
        .map_err(|error| map_ir_error(&error))?;
    value_to_py(py, &value)
}

/// A canonical inhabitant of `sort`, or `None` for a sort with none.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.ir")
)]
#[pyfunction]
pub fn well_founded_default<'py>(
    py: Python<'py>,
    arena: PyRef<'_, Arena>,
    sort: &crate::ir::types::PySort,
) -> PyResult<Option<Bound<'py, PyAny>>> {
    let sort: Sort = sort.resolve(arena.epoch)?;
    axeyum_ir::well_founded_default(&arena.arena, sort)
        .map(|value: Value| value_to_py(py, &value))
        .transpose()
}

/// Registers the evaluator surface on the `ir` submodule.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyAssignment>()?;
    module.add_function(wrap_pyfunction!(eval, module)?)?;
    module.add_function(wrap_pyfunction!(well_founded_default, module)?)?;
    Ok(())
}
