//! Configuration, verdicts, and the route trace.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use std::time::Duration;

use axeyum_solver::{
    BitLoweringMode, CheckResult, Model, SolverConfig, SolverError, UnknownKind, check_model,
};
use pyo3::prelude::*;
use pyo3::types::PyDict;

use crate::convert::{FuncValue, model_dict};
use crate::error::{AxeyumError, SmtLibParseError};
use crate::ir::arena::Arena;
use crate::ir::evaluate::PyAssignment;
use crate::ir::types::{Term, check_epoch};

/// Maps a Rust solver error onto the Python exception hierarchy.
pub(crate) fn map_solver_error(error: &SolverError) -> PyErr {
    match error {
        SolverError::Parse(what) => SmtLibParseError::new_err(what.clone()),
        other => AxeyumError::new_err(other.to_string()),
    }
}

/// The stable name of an `Unknown` cause.
pub(crate) fn unknown_kind_name(kind: UnknownKind) -> &'static str {
    match kind {
        UnknownKind::Timeout => "Timeout",
        UnknownKind::ResourceLimit => "ResourceLimit",
        UnknownKind::MemoryLimit => "MemoryLimit",
        UnknownKind::NodeBudget => "NodeBudget",
        UnknownKind::EncodingBudget => "EncodingBudget",
        UnknownKind::Incomplete => "Incomplete",
        _ => "Other",
    }
}

/// Every `Unknown` kind the solver classifies, in `UnknownKind` order.
pub(crate) const UNKNOWN_KINDS: &[&str] = &[
    "Timeout",
    "ResourceLimit",
    "MemoryLimit",
    "NodeBudget",
    "EncodingBudget",
    "Incomplete",
    "Other",
];

/// Per-query solver configuration.
///
/// Eighteen plain fields; the two `mpsc`-backed progress sinks
/// (`proof_progress`, `check_progress`) are deliberately **not** bound — they
/// are what make `SolverConfig` `!Sync`, and draining a Rust channel from
/// Python needs a design this slice does not have.
///
/// Every budget exhaustion surfaces as an `unknown`
/// [`CheckResult`](axeyum.solver.CheckResult), never as an exception.
// `unsendable`: `SolverConfig` holds two `Option<mpsc::Sender>` progress
// fields, which make it `Send` but `!Sync`. They are always `None` here (the
// sinks are not bound), but the type is what PyO3 checks. `unsendable` binds
// the object to the thread that created it, which is where a config is used.
#[pyclass(unsendable, from_py_object, module = "axeyum", name = "Config")]
#[derive(Clone)]
pub struct Config {
    pub(crate) config: SolverConfig,
}

impl Config {
    /// The configuration a `None` argument means: no budgets at all.
    pub(crate) fn resolve(config: Option<&Config>) -> SolverConfig {
        config.map_or_else(SolverConfig::new, |config| config.config.clone())
    }
}

#[pymethods]
impl Config {
    /// Builds a configuration. Every argument defaults to the Rust default.
    #[new]
    #[pyo3(signature = (
        *,
        timeout_ms = None,
        resource_limit = None,
        memory_limit_mb = None,
        node_budget = None,
        cnf_variable_budget = None,
        cnf_clause_budget = None,
        prove_unsat = false,
        cnf_inprocessing = false,
        cnf_vivify = false,
        preprocess = true,
        profile_bit_demand = false,
        profile_cnf_construction = false,
        bit_lowering_mode = "eager",
        incremental_positive_and_flattening = false,
        xor_cdcl_fallback = false,
        lazy_bv = false,
        native_cdcl = false,
        lazy_bv_abstract_ite = false,
    ))]
    #[allow(clippy::fn_params_excessive_bools, clippy::too_many_arguments)]
    fn new(
        timeout_ms: Option<u64>,
        resource_limit: Option<u64>,
        memory_limit_mb: Option<u64>,
        node_budget: Option<u64>,
        cnf_variable_budget: Option<u64>,
        cnf_clause_budget: Option<u64>,
        prove_unsat: bool,
        cnf_inprocessing: bool,
        cnf_vivify: bool,
        preprocess: bool,
        profile_bit_demand: bool,
        profile_cnf_construction: bool,
        bit_lowering_mode: &str,
        incremental_positive_and_flattening: bool,
        xor_cdcl_fallback: bool,
        lazy_bv: bool,
        native_cdcl: bool,
        lazy_bv_abstract_ite: bool,
    ) -> PyResult<Self> {
        let mode = match bit_lowering_mode {
            "eager" => BitLoweringMode::Eager,
            "demand_sliced" => BitLoweringMode::DemandSliced,
            other => {
                return Err(AxeyumError::new_err(format!(
                    "unknown bit_lowering_mode {other:?}; expected 'eager' or 'demand_sliced' \
                     ('range_sliced' needs a RangeDemandPolicy and is not bound in this slice)"
                )));
            }
        };
        let mut config = SolverConfig::new();
        config.timeout = timeout_ms.map(Duration::from_millis);
        config.resource_limit = resource_limit;
        config.memory_limit_mb = memory_limit_mb;
        config.node_budget = node_budget;
        config.cnf_variable_budget = cnf_variable_budget;
        config.cnf_clause_budget = cnf_clause_budget;
        config.prove_unsat = prove_unsat;
        config.cnf_inprocessing = cnf_inprocessing;
        config.cnf_vivify = cnf_vivify;
        config.preprocess = preprocess;
        config.profile_bit_demand = profile_bit_demand;
        config.profile_cnf_construction = profile_cnf_construction;
        config.bit_lowering_mode = mode;
        config.incremental_positive_and_flattening = incremental_positive_and_flattening;
        config.xor_cdcl_fallback = xor_cdcl_fallback;
        config.lazy_bv = lazy_bv;
        config.native_cdcl = native_cdcl;
        config.lazy_bv_abstract_ite = lazy_bv_abstract_ite;
        Ok(Self { config })
    }

    /// The wall-clock budget in milliseconds, or `None`.
    #[getter]
    fn timeout_ms(&self) -> Option<u128> {
        self.config.timeout.map(|timeout| timeout.as_millis())
    }

    /// Whether `unsat` must carry a checked DRAT proof.
    #[getter]
    fn prove_unsat(&self) -> bool {
        self.config.prove_unsat
    }

    /// Whether the word-level canonicalizer runs before dispatch.
    #[getter]
    fn preprocess(&self) -> bool {
        self.config.preprocess
    }

    /// The translation node budget, or `None`.
    #[getter]
    fn node_budget(&self) -> Option<u64> {
        self.config.node_budget
    }

    fn __repr__(&self) -> String {
        format!(
            "Config(timeout_ms={:?}, prove_unsat={}, preprocess={}, node_budget={:?})",
            self.config.timeout.map(|t| t.as_millis()),
            self.config.prove_unsat,
            self.config.preprocess,
            self.config.node_budget
        )
    }
}

/// The verdict of one satisfiability check.
///
/// A tagged value with three shapes: `Sat` (with a model), `Unsat`, and
/// `Unknown` (with a classified `kind` and a `detail`). **`Unknown` is never
/// an exception** — a budget-exhausted or incomplete run is a first-class
/// answer, and reading it as `unsat` is the mistake the structure exists to
/// prevent.
#[pyclass(module = "axeyum", name = "CheckResult")]
pub struct PyCheckResult {
    pub(crate) status: &'static str,
    pub(crate) model: Option<Model>,
    pub(crate) unknown_kind: Option<&'static str>,
    pub(crate) unknown_detail: Option<String>,
    pub(crate) epoch: u64,
}

impl PyCheckResult {
    /// Wraps a Rust verdict for the arena at `epoch`.
    pub(crate) fn build(epoch: u64, result: &CheckResult) -> Self {
        match result {
            CheckResult::Sat(model) => Self {
                status: "sat",
                model: Some(model.clone()),
                unknown_kind: None,
                unknown_detail: None,
                epoch,
            },
            CheckResult::Unsat => Self {
                status: "unsat",
                model: None,
                unknown_kind: None,
                unknown_detail: None,
                epoch,
            },
            CheckResult::Unknown(reason) => Self {
                status: "unknown",
                model: None,
                unknown_kind: Some(unknown_kind_name(reason.kind)),
                unknown_detail: Some(reason.detail.clone()),
                epoch,
            },
        }
    }
}

#[pymethods]
impl PyCheckResult {
    /// `"sat"`, `"unsat"` or `"unknown"`.
    #[getter]
    fn status(&self) -> &'static str {
        self.status
    }

    /// Whether this is a `sat`.
    fn is_sat(&self) -> bool {
        self.status == "sat"
    }

    /// Whether this is an `unsat`.
    fn is_unsat(&self) -> bool {
        self.status == "unsat"
    }

    /// Whether this is an `unknown`.
    fn is_unknown(&self) -> bool {
        self.status == "unknown"
    }

    /// The classified `Unknown` cause, or `None` for a decided query.
    #[getter]
    fn unknown_kind(&self) -> Option<&'static str> {
        self.unknown_kind
    }

    /// The backend detail behind an `Unknown`, or `None`.
    #[getter]
    fn unknown_detail(&self) -> Option<&str> {
        self.unknown_detail.as_deref()
    }

    /// `{declared name: value}` in declaration order; empty unless `sat`.
    ///
    /// Symbols the solver left unconstrained are omitted rather than
    /// defaulted; inventing a value would be a claim the solver did not make.
    fn model<'py>(&self, py: Python<'py>, arena: PyRef<'_, Arena>) -> PyResult<Bound<'py, PyDict>> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let Some(model) = self.model.as_ref() else {
            return Ok(PyDict::new(py));
        };
        let named = arena.named_values(|symbol| model.get(symbol));
        model_dict(py, &named)
    }

    /// `{declared function name: FuncValue}`; empty unless `sat`.
    fn functions<'py>(
        &self,
        py: Python<'py>,
        arena: PyRef<'_, Arena>,
    ) -> PyResult<Bound<'py, PyDict>> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let dict = PyDict::new(py);
        let Some(model) = self.model.as_ref() else {
            return Ok(dict);
        };
        for (func, value) in model.functions() {
            let (name, _params, _result) = arena.arena.function(func);
            dict.set_item(name, FuncValue::build(py, value)?)?;
        }
        Ok(dict)
    }

    /// The model as an [`Assignment`](axeyum.ir.Assignment) for `ir.eval`.
    fn to_assignment(&self, arena: PyRef<'_, Arena>) -> PyResult<PyAssignment> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let Some(model) = self.model.as_ref() else {
            return Ok(PyAssignment::empty(self.epoch));
        };
        Ok(PyAssignment::wrap(self.epoch, model.to_assignment()))
    }

    /// Re-checks the model against `assertions` with `axeyum_solver::check_model`.
    ///
    /// This is the canonical replay: `True` means the model genuinely
    /// satisfies the ORIGINAL terms. Raises `ValueError` on a non-`sat`
    /// verdict rather than returning `False`, because "there was nothing to
    /// replay" and "the replay disagreed" are different findings and only the
    /// second is a soundness signal.
    fn replay(
        &self,
        py: Python<'_>,
        arena: PyRef<'_, Arena>,
        assertions: Vec<Term>,
    ) -> PyResult<bool> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let Some(model) = self.model.as_ref() else {
            return Err(pyo3::exceptions::PyValueError::new_err(format!(
                "a {} result carries no model to replay; check `status` first",
                self.status
            )));
        };
        let ids = arena.resolve_terms(&assertions)?;
        // Split the borrow out of the `PyRef` guard before releasing the GIL:
        // the guard itself is not `Send`, but `&TermArena` and `&Model` are.
        let subject: &axeyum_ir::TermArena = &arena.arena;
        py.detach(|| check_model(subject, &ids, model))
            .map_err(|error| map_solver_error(&error))
    }

    fn __repr__(&self) -> String {
        match self.unknown_kind {
            Some(kind) => format!(
                "CheckResult(status='unknown', kind={kind:?}, detail={:?})",
                self.unknown_detail.as_deref().unwrap_or_default()
            ),
            None => format!("CheckResult(status={:?})", self.status),
        }
    }
}

/// The record of which routes the auto-dispatcher tried, and what each said.
///
/// Verdict-invariant with the un-traced dispatch: the recorder never
/// participates in a branch.
#[pyclass(frozen, module = "axeyum", name = "RouteTrace")]
pub struct PyRouteTrace {
    pub(crate) json: String,
    pub(crate) attempts: usize,
}

#[pymethods]
impl PyRouteTrace {
    /// The trace as JSON — the one native serializer in the solver surface.
    fn to_json(&self) -> &str {
        &self.json
    }

    /// Number of recorded route attempts.
    fn __len__(&self) -> usize {
        self.attempts
    }

    fn __repr__(&self) -> String {
        format!("RouteTrace(attempts={})", self.attempts)
    }
}
