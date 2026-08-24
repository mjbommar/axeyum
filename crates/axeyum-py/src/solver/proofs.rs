//! `axeyum.solver.proofs` — exportable `unsat` certificates and their checkers.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use std::time::{Duration, Instant};

use axeyum_solver::{UnsatProof, UnsatProofOutcome};
use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::ir::arena::Arena;
use crate::ir::types::Term;
use crate::solver::results::map_solver_error;

/// A checkable `unsat` certificate: the CNF and its refutation, as text.
///
/// Three plain strings, so a caller can write them to files and hand them to
/// `drat-trim` or any LRAT checker without this binding in the loop.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "UnsatProof")]
#[derive(Clone)]
pub struct PyUnsatProof {
    proof: UnsatProof,
}

impl PyUnsatProof {
    pub(crate) fn build(proof: UnsatProof) -> Self {
        Self { proof }
    }
}

#[pymethods]
impl PyUnsatProof {
    /// The bit-blasted CNF in DIMACS.
    #[getter]
    fn dimacs(&self) -> &str {
        &self.proof.dimacs
    }

    /// The DRAT refutation.
    #[getter]
    fn drat(&self) -> &str {
        &self.proof.drat
    }

    /// The LRAT refutation, or `None` when the proof could not be elaborated
    /// (a RAT step, say). **`None` is not `False`** — the DRAT certificate
    /// still stands.
    #[getter]
    fn lrat(&self) -> Option<&str> {
        self.proof.lrat.as_deref()
    }

    /// Re-derives the refutation from the certificate TEXT alone.
    ///
    /// Parses the DIMACS and the DRAT, then confirms the empty clause follows
    /// (RUP+RAT) — what an external `drat-trim` run would do. When an LRAT is
    /// also present it must independently confirm the same refutation; a
    /// present-but-failing LRAT rejects the whole certificate.
    fn recheck(&self, py: Python<'_>) -> PyResult<bool> {
        let proof = &self.proof;
        py.detach(|| proof.recheck())
            .map_err(|error| map_solver_error(&error))
    }

    /// Re-checks the LRAT certificate in linear time, or `None` when there is
    /// no LRAT.
    ///
    /// `None` is **never** coerced to `True`: "no certificate was checked" and
    /// "the certificate checked out" are different findings.
    fn recheck_lrat(&self, py: Python<'_>) -> PyResult<Option<bool>> {
        let proof = &self.proof;
        py.detach(|| proof.recheck_lrat())
            .map_err(|error| map_solver_error(&error))
    }

    fn __repr__(&self) -> String {
        format!(
            "UnsatProof(dimacs={} bytes, drat={} bytes, lrat={})",
            self.proof.dimacs.len(),
            self.proof.drat.len(),
            self.proof
                .lrat
                .as_ref()
                .map_or_else(|| "None".to_owned(), |lrat| format!("{} bytes", lrat.len()))
        )
    }
}

/// The outcome of attempting to export an `unsat` proof.
///
/// `Inconclusive` means the proof core exhausted its budget. **It is not a
/// pass and not a `sat`** — a timeout is a third answer.
#[pyclass(frozen, module = "axeyum", name = "UnsatProofOutcome")]
pub struct PyUnsatProofOutcome {
    status: &'static str,
    proof: Option<PyUnsatProof>,
}

impl PyUnsatProofOutcome {
    fn build(outcome: UnsatProofOutcome) -> Self {
        match outcome {
            UnsatProofOutcome::Proved(proof) => Self {
                status: "proved",
                proof: Some(PyUnsatProof::build(proof)),
            },
            UnsatProofOutcome::Satisfiable => Self {
                status: "satisfiable",
                proof: None,
            },
            UnsatProofOutcome::Inconclusive => Self {
                status: "inconclusive",
                proof: None,
            },
        }
    }
}

#[pymethods]
impl PyUnsatProofOutcome {
    /// `"proved"`, `"satisfiable"` or `"inconclusive"`.
    #[getter]
    fn status(&self) -> &'static str {
        self.status
    }

    /// The certificate, when `proved`.
    #[getter]
    fn proof(&self) -> Option<PyUnsatProof> {
        self.proof.clone()
    }

    /// Whether a certificate was produced.
    fn is_proved(&self) -> bool {
        self.status == "proved"
    }

    /// Whether the query was decided satisfiable, so no `unsat` proof exists.
    fn is_satisfiable(&self) -> bool {
        self.status == "satisfiable"
    }

    /// Whether the budget ran out. **Not a pass.**
    fn is_inconclusive(&self) -> bool {
        self.status == "inconclusive"
    }

    fn __repr__(&self) -> String {
        format!("UnsatProofOutcome(status={:?})", self.status)
    }
}

/// Builds the deadline `_within` wants from a millisecond budget.
fn deadline(timeout_ms: Option<u64>) -> Option<Instant> {
    timeout_ms.and_then(|ms| Instant::now().checked_add(Duration::from_millis(ms)))
}

/// Bit-blasts `assertions` and, when unsatisfiable, exports a DRAT-checked
/// certificate.
///
/// `timeout_ms` bounds only the proof SEARCH; when it expires the outcome is
/// `inconclusive`, which is neither a verdict nor a pass.
#[pyfunction]
#[pyo3(signature = (arena, assertions, timeout_ms = None))]
pub fn export_qf_bv_unsat_proof(
    py: Python<'_>,
    arena: PyRef<'_, Arena>,
    assertions: Vec<Term>,
    timeout_ms: Option<u64>,
) -> PyResult<PyUnsatProofOutcome> {
    let ids = arena.resolve_terms(&assertions)?;
    let subject: &axeyum_ir::TermArena = &arena.arena;
    let deadline = deadline(timeout_ms);
    let outcome = py
        .detach(|| axeyum_solver::export_qf_bv_unsat_proof_within(subject, &ids, deadline))
        .map_err(|error| map_solver_error(&error))?;
    Ok(PyUnsatProofOutcome::build(outcome))
}

/// Generates the `&mut TermArena` exporters (arrays, functions, datatypes).
macro_rules! mut_exporters {
    ($($py:ident => $rust:ident $(/ $within:ident)?),* $(,)?) => {
        $(
            #[doc = concat!("`axeyum_solver::", stringify!($rust), "`.\n\nAn exhausted budget is `inconclusive`, never a verdict.")]
            #[pyfunction]
            #[pyo3(signature = (arena, assertions, timeout_ms = None))]
            pub fn $py(
                py: Python<'_>,
                mut arena: PyRefMut<'_, Arena>,
                assertions: Vec<Term>,
                timeout_ms: Option<u64>,
            ) -> PyResult<PyUnsatProofOutcome> {
                let ids = arena.resolve_terms(&assertions)?;
                let deadline = deadline(timeout_ms);
                let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
                let outcome = py
                    .detach(move || {
                        mut_exporters!(@call subject, &ids, deadline, $rust $(, $within)?)
                    })
                    .map_err(|error| map_solver_error(&error))?;
                Ok(PyUnsatProofOutcome::build(outcome))
            }
        )*
    };
    (@call $arena:expr, $ids:expr, $deadline:expr, $rust:ident, $within:ident) => {
        match $deadline {
            Some(deadline) => axeyum_solver::$within($arena, $ids, Some(deadline)),
            None => axeyum_solver::$rust($arena, $ids),
        }
    };
    (@call $arena:expr, $ids:expr, $deadline:expr, $rust:ident) => {{
        let _ = $deadline;
        axeyum_solver::$rust($arena, $ids)
    }};
}

mut_exporters!(
    export_qf_abv_unsat_proof => export_qf_abv_unsat_proof / export_qf_abv_unsat_proof_within,
    export_qf_aufbv_unsat_proof => export_qf_aufbv_unsat_proof / export_qf_aufbv_unsat_proof_within,
    export_qf_uf_unsat_proof => export_qf_uf_unsat_proof,
    export_datatype_unsat_proof => export_datatype_unsat_proof,
);

/// `axeyum_solver::export_qf_lia_unsat_proof`.
///
/// `int_width` is the bit width the integers are blasted at; an `unsat` is
/// only an `unsat` **within that width**, which is why the parameter has no
/// default.
#[pyfunction]
pub fn export_qf_lia_unsat_proof(
    py: Python<'_>,
    mut arena: PyRefMut<'_, Arena>,
    assertions: Vec<Term>,
    int_width: u32,
) -> PyResult<PyUnsatProofOutcome> {
    let ids = arena.resolve_terms(&assertions)?;
    let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
    let outcome = py
        .detach(move || axeyum_solver::export_qf_lia_unsat_proof(subject, &ids, int_width))
        .map_err(|error| map_solver_error(&error))?;
    Ok(PyUnsatProofOutcome::build(outcome))
}

/// Builds the `solver.proofs` submodule.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.solver.proofs")?;
    module.add(
        "__doc__",
        "tier P + C -- exportable unsat certificates and their independent \
         re-checkers. Inconclusive is not a pass; no LRAT is None, not True.",
    )?;
    module.add_class::<PyUnsatProof>()?;
    module.add_class::<PyUnsatProofOutcome>()?;
    module.add_function(wrap_pyfunction!(export_qf_bv_unsat_proof, &module)?)?;
    module.add_function(wrap_pyfunction!(export_qf_abv_unsat_proof, &module)?)?;
    module.add_function(wrap_pyfunction!(export_qf_aufbv_unsat_proof, &module)?)?;
    module.add_function(wrap_pyfunction!(export_qf_uf_unsat_proof, &module)?)?;
    module.add_function(wrap_pyfunction!(export_qf_lia_unsat_proof, &module)?)?;
    module.add_function(wrap_pyfunction!(export_datatype_unsat_proof, &module)?)?;
    parent.add("proofs", &module)?;
    Ok(module)
}
