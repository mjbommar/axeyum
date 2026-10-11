//! Typed OMT outcomes keep feasibility replay distinct from optimality evidence.
#![allow(clippy::unused_self)] // PyO3 getters require a receiver for fixed evidence availability.
use super::{map_solver_error, script_config};
use crate::{convert::model_dict, stub_types::PyBigInt};
use axeyum_ir::{Sort, Value};
use axeyum_solver::{
    OptOutcome,
    smtlib::optimization::{
        OptimizationMode, OptimizationReport, optimize_with_models,
        portable::{CertificateCheckReport, OptimizationCertificate},
    },
};
use pyo3::{
    exceptions::{PyIndexError, PyValueError},
    prelude::*,
    types::PyModule,
};
use std::sync::Arc;

/// One optimization objective and its replayable feasible witness.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.smt")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "OptimizationObjective"
)]
#[derive(Debug, Clone)]
pub struct OptimizationObjective {
    report: Arc<OptimizationReport>,
    index: usize,
}
#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl OptimizationObjective {
    /// optimal, infeasible, unbounded or unknown; optimal is not a gold certificate.
    #[getter]
    fn status(&self) -> &'static str {
        match self.report.objectives[self.index].outcome {
            OptOutcome::Optimal(_) => "optimal",
            OptOutcome::Infeasible => "infeasible",
            OptOutcome::Unbounded => "unbounded",
            OptOutcome::Unknown(_) => "unknown",
        }
    }
    /// maximize or minimize.
    #[getter]
    fn direction(&self) -> &'static str {
        if self.report.objectives[self.index].maximize {
            "maximize"
        } else {
            "minimize"
        }
    }
    /// Int or BitVec; bit-vector optimization uses unsigned order.
    #[getter]
    fn sort(&self) -> &'static str {
        match self.report.objectives[self.index].sort {
            Sort::Int => "Int",
            Sort::BitVec(_) => "BitVec",
            _ => "unsupported",
        }
    }
    /// Bit-vector width, or None for an integer objective.
    #[getter]
    fn bit_width(&self) -> Option<u32> {
        match self.report.objectives[self.index].sort {
            Sort::BitVec(w) => Some(w),
            _ => None,
        }
    }
    /// Exact optimum as a Python int; BV values are unsigned. None if undecided.
    #[getter]
    fn value<'py>(&self, py: Python<'py>) -> PyResult<Option<PyBigInt<'py>>> {
        match &self.report.objectives[self.index].value {
            Some(Value::Int(v)) => Ok(Some(PyBigInt::new(v.into_pyobject(py)?.into_any()))),
            Some(Value::Bv { value, .. }) => {
                Ok(Some(PyBigInt::new(value.into_pyobject(py)?.into_any())))
            }
            _ => Ok(None),
        }
    }
    /// Unknown reason, empty for a decided optimization.
    #[getter]
    fn detail(&self) -> String {
        match &self.report.objectives[self.index].outcome {
            OptOutcome::Unknown(r) => r.detail.clone(),
            _ => String::new(),
        }
    }
    /// Whether this objective retains a model for replay.
    #[getter]
    fn model_available(&self) -> bool {
        self.report.objectives[self.index]
            .model_unavailable
            .is_none()
    }
    /// Why witness retrieval did not complete, or None when available.
    #[getter]
    fn model_unavailable_reason(&self) -> Option<String> {
        self.report.objectives[self.index].model_unavailable.clone()
    }
    /// A fresh declaration-ordered dictionary; mutation cannot alter replay state.
    #[getter]
    fn model<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, pyo3::types::PyDict>> {
        model_dict(py, &self.report.model_entries(self.index))
    }
    /// Replay original assertions, lexicographic prefix and claimed objective value.
    /// None means no witness, not a successful replay.
    fn replay(&self, py: Python<'_>) -> PyResult<Option<bool>> {
        py.detach(|| self.report.replay(self.index))
            .map_err(map_solver_error)
    }
    /// Rebuild and check the original strict-better query's refutation.
    /// None means missing evidence, including integer-only cut or BV routes.
    fn replay_optimality(&self, py: Python<'_>) -> PyResult<Option<bool>> {
        py.detach(|| self.report.replay_optimality(self.index))
            .map_err(map_solver_error)
    }
    /// Export bounded original-query evidence. Missing optimality evidence declines.
    /// Lexicographic exports include every earlier objective's witnesses.
    fn certificate_json(&self, py: Python<'_>) -> PyResult<String> {
        py.detach(|| self.report.certificate(self.index)?.to_json())
            .map_err(map_solver_error)
    }
    /// Replay both witnesses, including every earlier lexicographic objective.
    /// Missing or invalid evidence yields false; a model alone is insufficient.
    #[getter]
    fn gold_eligible(&self, py: Python<'_>) -> PyResult<bool> {
        py.detach(|| self.report.gold_eligible(self.index))
            .map_err(map_solver_error)
    }
}
/// Explicit box/lex semantics and ordered per-objective results.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.smt")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "OptimizationResult")]
#[derive(Debug, Clone)]
pub struct OptimizationResult {
    report: Arc<OptimizationReport>,
}
#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl OptimizationResult {
    /// Explicit lex or box semantics.
    #[getter]
    fn mode(&self) -> &'static str {
        self.report.mode.name()
    }
    /// Results in active objective declaration order.
    #[getter]
    fn objectives(&self) -> Vec<OptimizationObjective> {
        (0..self.report.objectives.len())
            .map(|index| OptimizationObjective {
                report: Arc::clone(&self.report),
                index,
            })
            .collect()
    }
    /// True when every objective has an optimum and retained feasible model.
    /// This is completion of witness retrieval, not checked optimality.
    #[getter]
    fn complete(&self) -> bool {
        !self.report.objectives.is_empty()
            && self.report.objectives.iter().all(|r| {
                matches!(r.outcome, OptOutcome::Optimal(_)) && r.model_unavailable.is_none()
            })
    }
    fn __len__(&self) -> usize {
        self.report.objectives.len()
    }
    fn __getitem__(&self, index: usize) -> PyResult<OptimizationObjective> {
        if index >= self.report.objectives.len() {
            return Err(PyIndexError::new_err("objective index"));
        }
        Ok(OptimizationObjective {
            report: Arc::clone(&self.report),
            index,
        })
    }
}
/// Optimize Int/unsigned-BV objectives explicitly. Feasible model replay is
/// provided; gold eligibility additionally rechecks source-bound refutations.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.smt")
)]
#[pyfunction]
#[pyo3(signature=(script,*,mode="lex",timeout_ms=2000,resource_limit=None,memory_limit_mb=None,node_budget=None,cnf_variable_budget=None,cnf_clause_budget=None))]
#[allow(clippy::too_many_arguments)]
fn optimize(
    py: Python<'_>,
    script: &str,
    mode: &str,
    timeout_ms: u64,
    resource_limit: Option<u64>,
    memory_limit_mb: Option<u64>,
    node_budget: Option<u64>,
    cnf_variable_budget: Option<u64>,
    cnf_clause_budget: Option<u64>,
) -> PyResult<OptimizationResult> {
    let mode = match mode {
        "lex" => OptimizationMode::Lexicographic,
        "box" => OptimizationMode::Box,
        _ => return Err(PyValueError::new_err("mode must be lex or box")),
    };
    let config = script_config(
        timeout_ms,
        resource_limit,
        memory_limit_mb,
        node_budget,
        cnf_variable_budget,
        cnf_clause_budget,
        false,
        true,
    );
    let report = py
        .detach(|| optimize_with_models(script, mode, &config))
        .map_err(map_solver_error)?;
    Ok(OptimizationResult {
        report: Arc::new(report),
    })
}
/// Counted original-query replay; parsing certificate data alone grants no acceptance.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.smt")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "OptimizationCertificateCheck"
)]
#[derive(Debug, Clone)]
pub struct OptimizationCertificateCheck {
    report: CertificateCheckReport,
}
#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl OptimizationCertificateCheck {
    /// True only after all required feasible-model and strict-better checks succeed.
    #[getter]
    fn accepted(&self) -> bool {
        self.report.accepted
    }
    /// Number of obligations actually examined.
    #[getter]
    fn examined(&self) -> usize {
        self.report.examined
    }
    /// Number of obligations successfully discharged.
    #[getter]
    fn discharged(&self) -> usize {
        self.report.discharged
    }
    /// Rejection reason, or None after complete acceptance.
    #[getter]
    fn reason(&self) -> Option<String> {
        self.report.reason.clone()
    }
}
/// Replay exported optimization JSON against the caller's original query.
/// Never runs optimization search. Malformed/unsupported evidence raises an error.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.smt")
)]
#[pyfunction]
fn check_optimization_certificate(
    py: Python<'_>,
    certificate_json: &str,
    script: &str,
) -> PyResult<OptimizationCertificateCheck> {
    let report = py
        .detach(|| OptimizationCertificate::from_json(certificate_json)?.check(script))
        .map_err(map_solver_error)?;
    Ok(OptimizationCertificateCheck { report })
}
pub(super) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<OptimizationResult>()?;
    module.add_class::<OptimizationCertificateCheck>()?;
    module.add_function(wrap_pyfunction!(check_optimization_certificate, module)?)?;
    module.add_class::<OptimizationObjective>()?;
    module.add_function(wrap_pyfunction!(optimize, module)?)?;
    Ok(())
}
