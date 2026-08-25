//! `axeyum.solver.cnf` — DIMACS, the independent DRAT checker, and the
//! proof-producing CDCL core.
//!
//! Tier **C** is the point of this module: `check_drat` is the trusted small
//! checker, and its `ResourceOut` / `Interrupted` outcomes are neither `True`
//! nor `False`.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfFormula, DratCheckOutcome, ProofSolveOutcome, check_drat,
    check_drat_with_limits_and_progress, parse_dimacs, parse_drat,
    solve_with_drat_proof_with_limits, solve_with_drat_proof_within, write_drat,
};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyModule};

use crate::error::AxeyumError;

/// A CNF formula in conjunctive normal form.
#[pyclass(module = "axeyum", name = "CnfFormula")]
pub struct PyCnfFormula {
    pub(crate) formula: CnfFormula,
}

#[pymethods]
impl PyCnfFormula {
    /// Number of declared variables.
    #[getter]
    fn variable_count(&self) -> usize {
        self.formula.variable_count()
    }

    /// Number of clauses.
    #[getter]
    fn clause_count(&self) -> usize {
        self.formula.clauses().len()
    }

    /// The clauses as DIMACS literal lists (`1`-based, negatives for negation).
    #[getter]
    fn clauses(&self) -> Vec<Vec<i64>> {
        self.formula
            .clauses()
            .iter()
            .map(|clause| clause.lits().iter().map(|lit| lit.dimacs()).collect())
            .collect()
    }

    /// The formula in DIMACS text. Byte-stable.
    fn to_dimacs(&self) -> String {
        self.formula.to_dimacs()
    }

    /// The formula in DIMACS, as `bytes`. Same bytes, byte-stable.
    ///
    /// The Rust renderer builds a `String` either way, so this saves the
    /// `PyUnicode` construction, not the render: `CPython` scans a `str` for its
    /// widest code point on creation, which is linear in a formula that can run
    /// to tens of megabytes, and every consumer of DIMACS (a file, a hash, a
    /// subprocess) wants bytes back immediately afterward.
    ///
    /// # Errors
    ///
    /// Propagates a Python allocation failure.
    fn to_dimacs_bytes<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        // Rendered without the GIL: it is a pure-Rust format over the clause
        // arena and is the expensive half for a large formula.
        let text = py.detach(|| self.formula.to_dimacs());
        PyBytes::new_with(py, text.len(), |slice| {
            slice.copy_from_slice(text.as_bytes());
            Ok(())
        })
    }

    /// Whether `assignment` (one bool per variable, in order) satisfies it.
    fn evaluate(&self, assignment: Vec<bool>) -> PyResult<bool> {
        self.formula
            .evaluate(&assignment)
            .map_err(|error| AxeyumError::new_err(error.to_string()))
    }

    fn __repr__(&self) -> String {
        format!(
            "CnfFormula(variables={}, clauses={})",
            self.formula.variable_count(),
            self.formula.clauses().len()
        )
    }
}

/// Parses DIMACS text into a formula.
#[pyfunction]
pub fn parse_dimacs_py(input: &str) -> PyResult<PyCnfFormula> {
    Ok(PyCnfFormula {
        formula: parse_dimacs(input).map_err(|error| AxeyumError::new_err(error.to_string()))?,
    })
}

/// The outcome of an independent DRAT check.
///
/// Three-valued: `ResourceOut` and `Interrupted` mean the checker did NOT
/// finish, which is neither "the proof is good" nor "the proof is bad".
/// Nothing here coerces to a `bool`.
#[pyclass(frozen, module = "axeyum", name = "DratCheckOutcome")]
pub struct PyDratCheckOutcome {
    status: &'static str,
    verified: Option<bool>,
}

#[pymethods]
impl PyDratCheckOutcome {
    /// `"verified"`, `"resource-out"` or `"interrupted"`.
    #[getter]
    fn status(&self) -> &'static str {
        self.status
    }

    /// Whether the refutation checked out, or `None` when the check did not
    /// finish. **`None` is not `False`.**
    #[getter]
    fn verified(&self) -> Option<bool> {
        self.verified
    }

    fn __repr__(&self) -> String {
        format!(
            "DratCheckOutcome(status={:?}, verified={:?})",
            self.status, self.verified
        )
    }
}

/// Independently re-checks a DRAT refutation of `formula` (RUP+RAT).
///
/// Returns a three-valued outcome. When `max_steps` or `timeout_ms` cuts the
/// run short the answer is `resource-out` / `interrupted`, never a verdict.
#[pyfunction]
#[pyo3(signature = (formula, drat, *, max_steps = None, timeout_ms = None))]
pub fn check_drat_py(
    py: Python<'_>,
    formula: PyRef<'_, PyCnfFormula>,
    drat: &str,
    max_steps: Option<usize>,
    timeout_ms: Option<u64>,
) -> PyResult<PyDratCheckOutcome> {
    let proof = parse_drat(drat).map_err(|error| AxeyumError::new_err(error.to_string()))?;
    let subject: &CnfFormula = &formula.formula;
    if max_steps.is_none() && timeout_ms.is_none() {
        let verified = py
            .detach(|| check_drat(subject, &proof))
            .map_err(|error| AxeyumError::new_err(error.to_string()))?;
        return Ok(PyDratCheckOutcome {
            status: "verified",
            verified: Some(verified),
        });
    }
    let deadline = timeout_ms.and_then(|ms| Instant::now().checked_add(Duration::from_millis(ms)));
    let outcome = py
        .detach(|| {
            check_drat_with_limits_and_progress(subject, &proof, deadline, max_steps, 0, None)
        })
        .map_err(|error| AxeyumError::new_err(error.to_string()))?;
    Ok(match outcome {
        DratCheckOutcome::Verified(verified) => PyDratCheckOutcome {
            status: "verified",
            verified: Some(verified),
        },
        DratCheckOutcome::ResourceOut => PyDratCheckOutcome {
            status: "resource-out",
            verified: None,
        },
        DratCheckOutcome::Interrupted => PyDratCheckOutcome {
            status: "interrupted",
            verified: None,
        },
    })
}

/// The outcome of the proof-producing CDCL core.
///
/// `ResourceOut` and `Interrupted` are UNDECIDED, so a caller mapping either
/// to `unknown` is sound; mapping them to a verdict is not.
#[pyclass(frozen, module = "axeyum", name = "ProofSolveOutcome")]
pub struct PyProofSolveOutcome {
    status: &'static str,
    assignment: Option<Vec<bool>>,
    drat: Option<String>,
}

#[pymethods]
impl PyProofSolveOutcome {
    /// `"sat"`, `"unsat"`, `"resource-out"` or `"interrupted"`.
    #[getter]
    fn status(&self) -> &'static str {
        self.status
    }

    /// The satisfying assignment, when `sat`.
    #[getter]
    fn assignment(&self) -> Option<&[bool]> {
        self.assignment.as_deref()
    }

    /// The DRAT refutation text, when `unsat`.
    #[getter]
    fn drat(&self) -> Option<&str> {
        self.drat.as_deref()
    }

    fn __repr__(&self) -> String {
        format!("ProofSolveOutcome(status={:?})", self.status)
    }
}

/// Solves `formula` with the DRAT-producing CDCL core (ADR-0012).
///
/// Never panics and never returns a `Result`: undecided is a verdict.
#[pyfunction]
#[pyo3(signature = (formula, *, timeout_ms = None, max_conflicts = None))]
pub fn solve_with_drat_proof(
    py: Python<'_>,
    formula: PyRef<'_, PyCnfFormula>,
    timeout_ms: Option<u64>,
    max_conflicts: Option<usize>,
) -> PyProofSolveOutcome {
    let deadline = timeout_ms.and_then(|ms| Instant::now().checked_add(Duration::from_millis(ms)));
    let subject: &CnfFormula = &formula.formula;
    let outcome = py.detach(|| match max_conflicts {
        Some(limit) => solve_with_drat_proof_with_limits(subject, deadline, limit),
        None => solve_with_drat_proof_within(subject, deadline),
    });
    match outcome {
        ProofSolveOutcome::Sat(assignment) => PyProofSolveOutcome {
            status: "sat",
            assignment: Some(assignment.values().to_vec()),
            drat: None,
        },
        ProofSolveOutcome::Unsat(steps) => PyProofSolveOutcome {
            status: "unsat",
            assignment: None,
            drat: Some(write_drat(&steps)),
        },
        ProofSolveOutcome::ResourceOut => PyProofSolveOutcome {
            status: "resource-out",
            assignment: None,
            drat: None,
        },
        ProofSolveOutcome::Interrupted => PyProofSolveOutcome {
            status: "interrupted",
            assignment: None,
            drat: None,
        },
    }
}

/// A Tseitin encoding of an AIG, with the maps that let it be replayed.
#[pyclass(module = "axeyum", name = "CnfEncoding")]
pub struct PyCnfEncoding {
    encoding: axeyum_cnf::CnfEncoding,
}

#[pymethods]
impl PyCnfEncoding {
    /// The encoded formula.
    fn formula(&self) -> PyResult<PyCnfFormula> {
        // `to_dimacs` is byte-stable by contract, so this round-trip is an
        // owned copy without requiring `CnfFormula: Clone`.
        parse_dimacs_py(&self.encoding.formula().to_dimacs())
    }

    /// Number of CNF variables.
    #[getter]
    fn variable_count(&self) -> usize {
        self.encoding.formula().variable_count()
    }

    /// Number of CNF clauses.
    #[getter]
    fn clause_count(&self) -> usize {
        self.encoding.formula().clauses().len()
    }

    /// The AIG node values a CNF assignment implies.
    ///
    /// The validating replay map — the "never drop lowering/lift maps" hard
    /// rule made concrete. `lowering` must be the one this encoding came from.
    fn aig_node_values_from_assignment(
        &self,
        lowering: PyRef<'_, crate::ir::lowering::PyBitLowering>,
        values: Vec<bool>,
    ) -> PyResult<Vec<bool>> {
        let assignment = axeyum_cnf::CnfAssignment::new(values);
        self.encoding
            .aig_node_values_from_assignment(lowering.lowering.aig(), &assignment)
            .map_err(|error| AxeyumError::new_err(error.to_string()))
    }

    fn __repr__(&self) -> String {
        format!(
            "CnfEncoding(variables={}, clauses={})",
            self.encoding.formula().variable_count(),
            self.encoding.formula().clauses().len()
        )
    }
}

/// Tseitin-encodes a bit lowering's circuit, with its root bits as outputs.
#[pyfunction]
pub fn tseitin_encode(
    lowering: PyRef<'_, crate::ir::lowering::PyBitLowering>,
) -> PyResult<PyCnfEncoding> {
    let roots: Vec<_> = lowering
        .lowering
        .roots()
        .iter()
        .flat_map(|root| root.bits().iter().copied())
        .collect();
    let encoding = axeyum_cnf::tseitin_encode(lowering.lowering.aig(), &roots)
        .map_err(|error| AxeyumError::new_err(error.to_string()))?;
    Ok(PyCnfEncoding { encoding })
}

/// Builds the `solver.cnf` submodule.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.solver.cnf")?;
    module.add(
        "__doc__",
        "tier C -- DIMACS, the independent DRAT checker, and the proof-producing \
         CDCL core. A budget miss is a third answer, never a verdict.",
    )?;
    module.add_class::<PyCnfFormula>()?;
    module.add_class::<PyDratCheckOutcome>()?;
    module.add_class::<PyProofSolveOutcome>()?;
    module.add_class::<PyCnfEncoding>()?;
    module.add_function(wrap_pyfunction!(parse_dimacs_py, &module)?)?;
    module.add_function(wrap_pyfunction!(check_drat_py, &module)?)?;
    module.add_function(wrap_pyfunction!(solve_with_drat_proof, &module)?)?;
    module.add_function(wrap_pyfunction!(tseitin_encode, &module)?)?;
    module.add("parse_dimacs", module.getattr("parse_dimacs_py")?)?;
    module.add("check_drat", module.getattr("check_drat_py")?)?;
    module.add(
        "DEFAULT_PROOF_SAT_CONFLICT_LIMIT",
        axeyum_cnf::DEFAULT_PROOF_SAT_CONFLICT_LIMIT,
    )?;
    module.add(
        "DEFAULT_PROGRESS_CONFLICT_INTERVAL",
        axeyum_cnf::DEFAULT_PROGRESS_CONFLICT_INTERVAL,
    )?;
    parent.add("cnf", &module)?;
    Ok(module)
}
