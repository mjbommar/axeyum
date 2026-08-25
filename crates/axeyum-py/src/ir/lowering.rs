//! `axeyum.ir.bv` — bit lowering, its two preflight guards, and the replay maps.
//!
//! # Why the preflight is not optional
//!
//! `axeyum_bv`'s lowerer `unreachable!()`s on `Int`, `Real`, `Array`, datatype,
//! uninterpreted and sequence sorts. That path is reachable from Python, so
//! [`lower_terms`] calls `first_unsupported_op` and `first_unsupported_sort`
//! **before** lowering and raises `SortError` instead of letting Rust panic.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use axeyum_bv::{BitLowering, first_unsupported_op, first_unsupported_sort, lower_terms};
use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::convert::value_to_py;
use crate::error::AxeyumError;
use crate::ir::arena::Arena;
use crate::ir::evaluate::PyAssignment;
use crate::ir::types::{PySort, SortError, Term, check_epoch, op_name};

/// The first subterm whose operator the bit-blaster cannot lower, as
/// `(term, op name)`, or `None`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.ir.bv")
)]
// `#[pyo3(name = ...)]`: the Rust name carries a `_py` disambiguator that no
// caller should see. Registering under the clean name makes the generated stub
// describe the name the API actually uses; the `_py` spelling stays bound in
// `register` as an alias of the SAME object, so nothing is removed.
#[pyfunction]
#[pyo3(name = "first_unsupported_op")]
pub fn first_unsupported_op_py(
    arena: PyRef<'_, Arena>,
    roots: Vec<Term>,
) -> PyResult<Option<(Term, String)>> {
    let ids = arena.resolve_terms(&roots)?;
    Ok(first_unsupported_op(&arena.arena, &ids)
        .map(|(term, op)| (Term::new(arena.epoch, term), op_name(op).to_owned())))
}

/// The first subterm whose sort the bit-blaster cannot represent, as
/// `(term, sort)`, or `None`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.ir.bv")
)]
// `#[pyo3(name = ...)]`: the Rust name carries a `_py` disambiguator that no
// caller should see. Registering under the clean name makes the generated stub
// describe the name the API actually uses; the `_py` spelling stays bound in
// `register` as an alias of the SAME object, so nothing is removed.
#[pyfunction]
#[pyo3(name = "first_unsupported_sort")]
pub fn first_unsupported_sort_py(
    arena: PyRef<'_, Arena>,
    roots: Vec<Term>,
) -> PyResult<Option<(Term, PySort)>> {
    let ids = arena.resolve_terms(&roots)?;
    Ok(
        first_unsupported_sort(&arena.arena, &ids).map(|(term, sort)| {
            (
                Term::new(arena.epoch, term),
                PySort::bound(arena.epoch, sort),
            )
        }),
    )
}

/// A bit-blasted circuit together with the maps needed to replay it.
///
/// The lowering maps are the concrete form of the "never drop lowering/lift
/// maps after solving" hard rule: [`evaluate_root`](Self::evaluate_root) and
/// [`assignment_from_aig_values`](Self::assignment_from_aig_values) are how a
/// caller checks a circuit-level answer against the original terms.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir.bv")
)]
#[pyclass(module = "axeyum", name = "BitLowering")]
pub struct PyBitLowering {
    pub(crate) lowering: BitLowering,
    pub(crate) epoch: u64,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyBitLowering {
    /// Number of AIG nodes in the lowered circuit.
    #[getter]
    fn node_count(&self) -> usize {
        self.lowering.aig().node_count()
    }

    /// Number of circuit inputs (symbol bits).
    #[getter]
    fn input_count(&self) -> usize {
        self.lowering.aig().input_count()
    }

    /// Number of lowered roots.
    #[getter]
    fn root_count(&self) -> usize {
        self.lowering.roots().len()
    }

    /// The `(term, sort, bit count)` of each lowered root, in order.
    #[getter]
    fn roots(&self) -> Vec<(Term, PySort, usize)> {
        self.lowering
            .roots()
            .iter()
            .map(|root| {
                (
                    Term::new(self.epoch, root.term()),
                    PySort::bound(self.epoch, root.sort()),
                    root.bits().len(),
                )
            })
            .collect()
    }

    /// Evaluates lowered root `index` through the circuit under `assignment`.
    ///
    /// The answer must agree with `ir.eval` on the same term — that agreement
    /// is what makes the lowering checkable.
    fn evaluate_root<'py>(
        &self,
        py: Python<'py>,
        index: usize,
        assignment: PyRef<'_, PyAssignment>,
    ) -> PyResult<Bound<'py, PyAny>> {
        check_epoch(self.epoch, assignment.epoch, "Assignment")?;
        let value = self
            .lowering
            .evaluate_root(index, &assignment.assignment)
            .map_err(|error| AxeyumError::new_err(error.to_string()))?;
        value_to_py(py, &value)
    }

    /// Lifts a circuit-level input assignment back to an IR
    /// [`Assignment`](axeyum.ir.Assignment) over the original symbols.
    fn assignment_from_aig_values(&self, values: Vec<bool>) -> PyResult<PyAssignment> {
        let assignment = self
            .lowering
            .assignment_from_aig_values(&values)
            .map_err(|error| AxeyumError::new_err(error.to_string()))?;
        Ok(PyAssignment::wrap(self.epoch, assignment))
    }

    /// The circuit input bits implied by an IR assignment.
    fn input_values(&self, assignment: PyRef<'_, PyAssignment>) -> PyResult<Vec<bool>> {
        check_epoch(self.epoch, assignment.epoch, "Assignment")?;
        self.lowering
            .input_values(&assignment.assignment)
            .map_err(|error| AxeyumError::new_err(error.to_string()))
    }

    /// The circuit in ASCII AIGER (`aag`) form, with every root bit as an
    /// output. Deterministic, and it cannot fail.
    fn to_aiger_ascii(&self) -> String {
        let outputs: Vec<_> = self
            .lowering
            .roots()
            .iter()
            .flat_map(|root| root.bits().iter().copied())
            .collect();
        self.lowering.aig().to_aiger_ascii(&outputs)
    }

    fn __repr__(&self) -> String {
        format!(
            "BitLowering(nodes={}, inputs={}, roots={})",
            self.lowering.aig().node_count(),
            self.lowering.aig().input_count(),
            self.lowering.roots().len()
        )
    }
}

/// Bit-blasts `roots` into an AIG, after the two preflight guards pass.
///
/// # Errors
///
/// Raises `SortError` naming the offending subterm when the query is outside
/// the bit-blastable fragment; the Rust lowerer would otherwise panic.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.ir.bv")
)]
// `#[pyo3(name = ...)]`: the Rust name carries a `_py` disambiguator that no
// caller should see. Registering under the clean name makes the generated stub
// describe the name the API actually uses; the `_py` spelling stays bound in
// `register` as an alias of the SAME object, so nothing is removed.
#[pyfunction]
#[pyo3(name = "lower_terms")]
pub fn lower_terms_py(arena: PyRef<'_, Arena>, roots: Vec<Term>) -> PyResult<PyBitLowering> {
    let ids = arena.resolve_terms(&roots)?;
    if let Some((term, op)) = first_unsupported_op(&arena.arena, &ids) {
        return Err(SortError::new_err(format!(
            "operator `{}` at term #{} cannot be bit-blasted (preflight refused before the Rust \
             lowerer's unreachable!())",
            op_name(op),
            term.index()
        )));
    }
    if let Some((term, sort)) = first_unsupported_sort(&arena.arena, &ids) {
        return Err(SortError::new_err(format!(
            "sort {sort} at term #{} cannot be bit-blasted (preflight refused before the Rust \
             lowerer's unreachable!())",
            term.index()
        )));
    }
    let lowering =
        lower_terms(&arena.arena, &ids).map_err(|error| AxeyumError::new_err(error.to_string()))?;
    Ok(PyBitLowering {
        lowering,
        epoch: arena.epoch,
    })
}

/// Builds the `ir.bv` submodule.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.ir.bv")?;
    module.add(
        "__doc__",
        "tier P + C -- bit lowering, its two preflight guards, and the replay maps.",
    )?;
    module.add_class::<PyBitLowering>()?;
    module.add_function(wrap_pyfunction!(lower_terms_py, &module)?)?;
    module.add_function(wrap_pyfunction!(first_unsupported_op_py, &module)?)?;
    module.add_function(wrap_pyfunction!(first_unsupported_sort_py, &module)?)?;
    // Backwards-compatible aliases under the Rust fn names. They are the SAME
    // function objects, so a checked consumer reads the clean name and nothing
    // that used the `_py` spelling breaks.
    module.add("lower_terms_py", module.getattr("lower_terms")?)?;
    module.add(
        "first_unsupported_op_py",
        module.getattr("first_unsupported_op")?,
    )?;
    module.add(
        "first_unsupported_sort_py",
        module.getattr("first_unsupported_sort")?,
    )?;
    parent.add("bv", &module)?;
    Ok(module)
}
