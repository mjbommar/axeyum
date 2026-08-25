//! Solving, incremental solving, evidence, and the read-only metadata tables.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use axeyum_solver::{
    Evidence, EvidenceCheck, EvidenceReport, IncrementalBvSolver, ProofOutcome,
    ReplayCheckedSatCachePolicy, SolverConfig, Strategy,
};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyModule};

use crate::error::{AxeyumError, InternalError};
use crate::ir::arena::Arena;
use crate::ir::types::{Term, check_epoch};
use crate::solver::ledgers::PyTrustStep;
use crate::solver::proofs::PyUnsatProof;
use crate::solver::results::{Config, PyCheckResult, PyRouteTrace, map_solver_error};

/// Parses a strategy name.
fn strategy_from_name(name: &str) -> PyResult<Strategy> {
    match name {
        "eager_pure_rust" => Ok(Strategy::EagerPureRust),
        "lazy_bv_abstraction" => Ok(Strategy::LazyBvAbstraction),
        "auto" => Ok(Strategy::Auto),
        other => Err(AxeyumError::new_err(format!(
            "unknown strategy {other:?}; expected one of 'eager_pure_rust', \
             'lazy_bv_abstraction', 'auto' ('oracle' needs the z3 wheel)"
        ))),
    }
}

/// The stable name of a strategy.
fn strategy_name(strategy: Strategy) -> &'static str {
    match strategy {
        Strategy::EagerPureRust => "eager_pure_rust",
        Strategy::LazyBvAbstraction => "lazy_bv_abstraction",
        Strategy::Auto => "auto",
        // `Strategy` is `#[non_exhaustive]`; a name we do not know is reported
        // rather than silently mapped onto one we do.
        _ => "unrecognized",
    }
}

/// Runs one `axeyum_solver` dispatch with a panic caught and typed.
///
/// # Why `catch_unwind` here and a preflight everywhere else
///
/// Everywhere the binding CAN name the bad input first, it does: the bit
/// lowerer gets `first_unsupported_op`/`first_unsupported_sort`, `write_script`
/// gets an epoch check, the rational constructors get a zero-denominator test.
/// A preflight names the caller's mistake; a caught panic can only report that
/// something broke.
///
/// The multi-theory dispatcher is the case where a preflight is not available,
/// and the reason is that the SAME sort is fine or fatal depending on a route
/// chosen inside Rust. Measured 2026-08-25: `(= s1 s2)` over two `String`
/// symbols reaches `axeyum-bv`'s `unreachable!("sequence terms are rejected
/// before bit lowering (P2.7)")` through `solve`, `check_auto_explained` and
/// `unsat_core`, while `(= (str.len s) 1)` -- a sequence term in the same
/// query, over the same sort -- is dispatched to arithmetic and answers
/// normally. Refusing every sequence-bearing query up front would therefore
/// break queries that work today, and refusing none of them lets a
/// `PanicException` escape `except Exception`.
///
/// So the panic is caught HERE, at the single dispatch call, and nowhere else.
/// It is deliberately NOT a blanket wrapper around the module: a panic anywhere
/// the binding has not measured must stay loud. `InternalError` names the Rust
/// site and says it is a bug in Axeyum, so nothing about this is quiet.
///
/// `AssertUnwindSafe` is required because `&mut TermArena` is not
/// `UnwindSafe`. That is sound here for the reason the marker exists: this
/// process observes the arena again only through Python, and a caller who has
/// just been told the engine broke has no invariant left to rely on. It is a
/// safe API -- `unsafe_code` stays denied.
fn dispatch<T>(site: &'static str, work: impl FnOnce() -> T) -> PyResult<T> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(work)).map_err(|payload| {
        let detail = payload
            .downcast_ref::<&str>()
            .map(|text| (*text).to_owned())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "panic payload was not a string".to_owned());
        InternalError::new_err(format!(
            "{site} panicked: {detail}. This is a bug in Axeyum, not in the query; the panic was \
             converted so it does not escape `except Exception` as a PanicException"
        ))
    })
}

/// Decides `assertions` with the multi-theory dispatcher.
///
/// `unknown` comes back as a [`CheckResult`](axeyum.solver.CheckResult), never
/// as an exception.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
#[pyo3(signature = (arena, assertions, config = None))]
pub fn solve(
    py: Python<'_>,
    mut arena: PyRefMut<'_, Arena>,
    assertions: Vec<Term>,
    config: Option<&Config>,
) -> PyResult<PyCheckResult> {
    let epoch = arena.epoch;
    let ids = arena.resolve_terms(&assertions)?;
    let config = Config::resolve(config);
    // The `PyRefMut` guard is not `Send`, but `&mut TermArena` is; splitting the
    // borrow out is what lets the search run with the GIL released.
    let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
    let result = dispatch("axeyum_solver::solve", move || {
        py.detach(move || axeyum_solver::solve(subject, &ids, &config))
    })?
    .map_err(|error| map_solver_error(&error))?;
    Ok(PyCheckResult::build(epoch, &result))
}

/// Decides `assertions` and returns the route trace alongside the verdict.
///
/// The two are verdict-invariant with [`solve`]. **Read the trace as a record
/// of what was tried, not as "what axeyum answers for this script"** — the
/// SMT-LIB front door reaches routes this flat-term dispatcher does not.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
#[pyo3(signature = (arena, assertions, config = None))]
pub fn check_auto_explained(
    py: Python<'_>,
    mut arena: PyRefMut<'_, Arena>,
    assertions: Vec<Term>,
    config: Option<&Config>,
) -> PyResult<(PyCheckResult, PyRouteTrace)> {
    let epoch = arena.epoch;
    let ids = arena.resolve_terms(&assertions)?;
    let config = Config::resolve(config);
    let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
    let (result, trace) = dispatch("axeyum_solver::check_auto_explained", move || {
        py.detach(move || axeyum_solver::check_auto_explained(subject, &ids, &config))
    })?
    .map_err(|error| map_solver_error(&error))?;
    Ok((
        PyCheckResult::build(epoch, &result),
        PyRouteTrace {
            json: trace.to_json(),
            attempts: trace.attempts().len(),
        },
    ))
}

/// A deletion-minimized unsatisfiable core, as INDICES into `assertions`.
///
/// `None` when the query is not `unsat` (or the core could not be minimized).
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
#[pyo3(signature = (arena, assertions, config = None))]
pub fn unsat_core(
    py: Python<'_>,
    mut arena: PyRefMut<'_, Arena>,
    assertions: Vec<Term>,
    config: Option<&Config>,
) -> PyResult<Option<Vec<usize>>> {
    let ids = arena.resolve_terms(&assertions)?;
    let config = Config::resolve(config);
    let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
    dispatch("axeyum_solver::unsat_core", move || {
        py.detach(move || axeyum_solver::unsat_core(subject, &ids, &config))
    })?
    .map_err(|error| map_solver_error(&error))
}

/// Decides `assertions` with one named strategy.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
#[pyo3(signature = (arena, assertions, strategy, config = None))]
pub fn solve_with_strategy(
    py: Python<'_>,
    mut arena: PyRefMut<'_, Arena>,
    assertions: Vec<Term>,
    strategy: &str,
    config: Option<&Config>,
) -> PyResult<PyCheckResult> {
    let epoch = arena.epoch;
    let ids = arena.resolve_terms(&assertions)?;
    let config = Config::resolve(config);
    let strategy = strategy_from_name(strategy)?;
    let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
    let result = dispatch("axeyum_solver::solve_with_strategy", move || {
        py.detach(move || axeyum_solver::solve_with_strategy(subject, &ids, &config, strategy))
    })?
    .map_err(|error| map_solver_error(&error))?;
    Ok(PyCheckResult::build(epoch, &result))
}

/// Runs a portfolio of strategies in order and returns the first decision.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
#[pyo3(signature = (arena, assertions, strategies, config = None))]
pub fn solve_with_portfolio(
    py: Python<'_>,
    mut arena: PyRefMut<'_, Arena>,
    assertions: Vec<Term>,
    strategies: Vec<String>,
    config: Option<&Config>,
) -> PyResult<PyCheckResult> {
    let epoch = arena.epoch;
    let ids = arena.resolve_terms(&assertions)?;
    let config = Config::resolve(config);
    let strategies: Vec<Strategy> = strategies
        .iter()
        .map(|name| strategy_from_name(name))
        .collect::<PyResult<_>>()?;
    let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
    let result = dispatch("axeyum_solver::solve_with_portfolio", move || {
        py.detach(move || axeyum_solver::solve_with_portfolio(subject, &ids, &config, &strategies))
    })?
    .map_err(|error| map_solver_error(&error))?;
    Ok(PyCheckResult::build(epoch, &result))
}

/// The strategy order this query's shape recommends. Pure; decides nothing.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
pub fn recommended_portfolio(
    arena: PyRef<'_, Arena>,
    assertions: Vec<Term>,
) -> PyResult<Vec<&'static str>> {
    let ids = arena.resolve_terms(&assertions)?;
    Ok(axeyum_solver::recommended_portfolio(&arena.arena, &ids)
        .into_iter()
        .map(strategy_name)
        .collect())
}

/// The result of independently re-validating an [`Evidence`].
///
/// Three-valued on purpose. A `bool` cannot tell "I re-derived the
/// certificate" from "there was no certificate", and collapsing the second
/// into a pass is exactly the checker-that-cannot-fail defect. There is no
/// `__bool__` on this class for the same reason.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.solver")
)]
#[pyclass(frozen, module = "axeyum", name = "EvidenceCheck")]
pub struct PyEvidenceCheck {
    status: &'static str,
    reason: Option<&'static str>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyEvidenceCheck {
    /// `"verified"`, `"nothing-to-check"` or `"failed"`.
    #[getter]
    fn status(&self) -> &'static str {
        self.status
    }

    /// Why nothing was re-validated (`"uncertified-unsat"`, `"undecided"`,
    /// `"empty-subject"`, `"unfaithful-subject"`), else `None`.
    #[getter]
    fn reason(&self) -> Option<&'static str> {
        self.reason
    }

    /// Whether a certificate was present and re-derived THIS RUN. The only
    /// value that licenses trusting the result on the evidence alone.
    fn is_verified(&self) -> bool {
        self.status == "verified"
    }

    /// Whether the checker had nothing to re-validate. **Not a pass.**
    fn is_nothing_to_check(&self) -> bool {
        self.status == "nothing-to-check"
    }

    /// Whether a present certificate FAILED re-validation — a soundness alarm.
    fn is_failed(&self) -> bool {
        self.status == "failed"
    }

    fn __repr__(&self) -> String {
        match self.reason {
            Some(reason) => format!("EvidenceCheck(status='nothing-to-check', reason={reason:?})"),
            None => format!("EvidenceCheck(status={:?})", self.status),
        }
    }
}

impl PyEvidenceCheck {
    fn build(outcome: EvidenceCheck) -> Self {
        match outcome {
            EvidenceCheck::Verified => Self {
                status: "verified",
                reason: None,
            },
            EvidenceCheck::NothingToCheck(reason) => Self {
                status: "nothing-to-check",
                reason: Some(reason.label()),
            },
            EvidenceCheck::Failed => Self {
                status: "failed",
                reason: None,
            },
        }
    }
}

/// A verdict together with its checkable justification and provenance.
///
/// The primary "give me a checkable answer" API. `check_outcome` is what is
/// bound; the `bool`-returning `Evidence::check` is not, because it collapses
/// `NothingToCheck` into a pass.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.solver")
)]
#[pyclass(module = "axeyum", name = "EvidenceReport")]
pub struct PyEvidenceReport {
    report: EvidenceReport,
    epoch: u64,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyEvidenceReport {
    /// `"sat"`, `"unsat"` or `"unknown"`.
    #[getter]
    fn verdict(&self) -> &'static str {
        match &self.report.evidence {
            Evidence::Sat(_) => "sat",
            Evidence::Unknown(_) => "unknown",
            _ => "unsat",
        }
    }

    /// The stable label of the evidence variant (`"sat"`, `"unsat-drat"`,
    /// `"unsat-farkas"`, …) — what KIND of justification this is.
    #[getter]
    fn evidence_kind(&self) -> &'static str {
        self.report.evidence.kind_label()
    }

    /// Whether the evidence carries a transferable certificate at all.
    ///
    /// `False` on a bare `unsat` means the verdict is the deciding engine's
    /// with nothing re-derived — sound if the engine is, but unchecked.
    fn is_certified(&self) -> bool {
        self.report.evidence.is_certified()
    }

    /// The verdict as a [`CheckResult`](axeyum.solver.CheckResult).
    #[getter]
    fn result(&self) -> PyCheckResult {
        match &self.report.evidence {
            Evidence::Sat(model) => PyCheckResult {
                status: "sat",
                model: Some(model.clone()),
                unknown_kind: None,
                unknown_detail: None,
                epoch: self.epoch,
            },
            Evidence::Unknown(reason) => PyCheckResult {
                status: "unknown",
                model: None,
                unknown_kind: Some(crate::solver::results::unknown_kind_name(reason.kind)),
                unknown_detail: Some(reason.detail.clone()),
                epoch: self.epoch,
            },
            _ => PyCheckResult {
                status: "unsat",
                model: None,
                unknown_kind: None,
                unknown_detail: None,
                epoch: self.epoch,
            },
        }
    }

    /// The DRAT certificate, when the evidence is a plain proved `unsat`.
    #[getter]
    fn proof(&self) -> Option<PyUnsatProof> {
        match &self.report.evidence {
            Evidence::Unsat(Some(proof)) => Some(PyUnsatProof::build(proof.clone())),
            _ => None,
        }
    }

    /// Version and budget provenance, as a plain dict.
    #[getter]
    fn provenance<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        let dict = PyDict::new(py);
        let provenance = &self.report.provenance;
        dict.set_item("semantics_version", provenance.semantics_version)?;
        dict.set_item("backend", provenance.backend.clone())?;
        dict.set_item("assertion_count", provenance.assertion_count)?;
        dict.set_item(
            "timeout_ms",
            provenance.timeout.map(|timeout| timeout.as_millis()),
        )?;
        dict.set_item("resource_limit", provenance.resource_limit)?;
        dict.set_item("node_budget", provenance.node_budget)?;
        dict.set_item("cnf_variable_budget", provenance.cnf_variable_budget)?;
        dict.set_item("cnf_clause_budget", provenance.cnf_clause_budget)?;
        dict.set_item("prove_unsat", provenance.prove_unsat)?;
        Ok(dict)
    }

    /// The trusted reductions this result depended on, as
    /// `(label, certified_this_run)` in canonical order.
    ///
    /// `certified == False` names a reduction that was TRUSTED, not checked.
    #[getter]
    fn trusted_steps(&self) -> Vec<(&'static str, bool)> {
        self.report
            .trusted_steps
            .iter()
            .map(|step| (step.id.label(), step.certified))
            .collect()
    }

    /// The trusted reductions this result depended on, as structured
    /// [`TrustStep`](axeyum.solver.TrustStep) records in canonical order.
    ///
    /// The same list as `trusted_steps`, with the reduction's meaning,
    /// pedantic level, ADR and LEDGER-wide `is_certified()` bit alongside the
    /// PER-RUN `certified` one. Read `certified` to know what this result
    /// carried; `ledger_certified` answers a different question and a row
    /// where the two disagree is the normal case, not an anomaly.
    #[getter]
    fn trust_steps(&self) -> Vec<PyTrustStep> {
        self.report
            .trusted_steps
            .iter()
            .map(|&step| PyTrustStep::build(step))
            .collect()
    }

    /// Independently re-validates the evidence against `(arena, assertions)`.
    ///
    /// Returns the three-valued [`EvidenceCheck`](axeyum.solver.EvidenceCheck).
    fn check_outcome(
        &self,
        py: Python<'_>,
        arena: PyRef<'_, Arena>,
        assertions: Vec<Term>,
    ) -> PyResult<PyEvidenceCheck> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let ids = arena.resolve_terms(&assertions)?;
        let evidence = &self.report.evidence;
        let subject: &axeyum_ir::TermArena = &arena.arena;
        let outcome = py
            .detach(|| evidence.check_outcome(subject, &ids))
            .map_err(|error| map_solver_error(&error))?;
        Ok(PyEvidenceCheck::build(outcome))
    }

    fn __repr__(&self) -> String {
        format!(
            "EvidenceReport(verdict={:?}, evidence_kind={:?}, certified={})",
            self.verdict(),
            self.evidence_kind(),
            self.is_certified()
        )
    }
}

/// Decides `assertions` and returns the verdict WITH its justification.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
#[pyo3(signature = (arena, assertions, config = None))]
pub fn produce_evidence(
    py: Python<'_>,
    mut arena: PyRefMut<'_, Arena>,
    assertions: Vec<Term>,
    config: Option<&Config>,
) -> PyResult<PyEvidenceReport> {
    let epoch = arena.epoch;
    let ids = arena.resolve_terms(&assertions)?;
    let config = Config::resolve(config);
    let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
    let report = py
        .detach(move || axeyum_solver::produce_evidence(subject, &ids, &config))
        .map_err(|error| map_solver_error(&error))?;
    Ok(PyEvidenceReport { report, epoch })
}

/// The outcome of proving `goal` from `hypotheses`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.solver")
)]
#[pyclass(module = "axeyum", name = "ProofOutcome")]
pub struct PyProofOutcome {
    status: &'static str,
    report: Option<PyEvidenceReport>,
    countermodel: Option<PyCheckResult>,
    unknown_kind: Option<&'static str>,
    unknown_detail: Option<String>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyProofOutcome {
    /// `"proved"`, `"disproved"` or `"unknown"`.
    #[getter]
    fn status(&self) -> &'static str {
        self.status
    }

    /// The refutation of `hypotheses AND NOT goal`, when `proved`.
    ///
    /// `proved` alone is not "independently verified" — ask the report's
    /// `is_certified()` or re-run `check_outcome()`.
    #[getter]
    fn report(&self, py: Python<'_>) -> Option<Py<PyEvidenceReport>> {
        self.report.as_ref().and_then(|report| {
            Py::new(
                py,
                PyEvidenceReport {
                    report: report.report.clone(),
                    epoch: report.epoch,
                },
            )
            .ok()
        })
    }

    /// The counter-model satisfying the hypotheses and falsifying the goal.
    #[getter]
    fn countermodel(&self, py: Python<'_>) -> Option<Py<PyCheckResult>> {
        self.countermodel.as_ref().and_then(|result| {
            Py::new(
                py,
                PyCheckResult {
                    status: result.status,
                    model: result.model.clone(),
                    unknown_kind: result.unknown_kind,
                    unknown_detail: result.unknown_detail.clone(),
                    epoch: result.epoch,
                },
            )
            .ok()
        })
    }

    /// The classified reason the attempt was undecided, or `None`.
    #[getter]
    fn unknown_kind(&self) -> Option<&'static str> {
        self.unknown_kind
    }

    /// The backend detail behind an undecided attempt, or `None`.
    #[getter]
    fn unknown_detail(&self) -> Option<&str> {
        self.unknown_detail.as_deref()
    }

    fn __repr__(&self) -> String {
        format!("ProofOutcome(status={:?})", self.status)
    }
}

/// Proves `goal` from `hypotheses` by refuting `hypotheses AND NOT goal`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
#[pyo3(signature = (arena, hypotheses, goal, config = None))]
pub fn prove(
    py: Python<'_>,
    mut arena: PyRefMut<'_, Arena>,
    hypotheses: Vec<Term>,
    goal: Term,
    config: Option<&Config>,
) -> PyResult<PyProofOutcome> {
    let epoch = arena.epoch;
    let hypotheses = arena.resolve_terms(&hypotheses)?;
    let goal = goal.resolve(epoch)?;
    let config = Config::resolve(config);
    let subject: &mut axeyum_ir::TermArena = &mut arena.arena;
    let outcome = py
        .detach(move || axeyum_solver::prove(subject, &hypotheses, goal, &config))
        .map_err(|error| map_solver_error(&error))?;
    Ok(match outcome {
        ProofOutcome::Proved(report) => PyProofOutcome {
            status: "proved",
            report: Some(PyEvidenceReport {
                report: *report,
                epoch,
            }),
            countermodel: None,
            unknown_kind: None,
            unknown_detail: None,
        },
        ProofOutcome::Disproved(model) => PyProofOutcome {
            status: "disproved",
            report: None,
            countermodel: Some(PyCheckResult {
                status: "sat",
                model: Some(model),
                unknown_kind: None,
                unknown_detail: None,
                epoch,
            }),
            unknown_kind: None,
            unknown_detail: None,
        },
        ProofOutcome::Unknown(reason) => PyProofOutcome {
            status: "unknown",
            report: None,
            countermodel: None,
            unknown_kind: Some(crate::solver::results::unknown_kind_name(reason.kind)),
            unknown_detail: Some(reason.detail),
        },
    })
}

/// A warm, push/pop-capable bit-vector solver over ONE arena.
///
/// The Rust solver reuses arena-stable term ids and a persistent lowering, so
/// it is bound to a single arena for its whole life. Every method takes the
/// arena and asserts it is that one; a foreign arena raises `EpochError`.
// `unsendable`: the warm solver embeds a BatSat solver whose callback structs
// hold `Cell`s, so it is `Send` but `!Sync`. Binding it to its creating thread
// is exactly right for an object that is also bound to one arena.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.solver")
)]
#[pyclass(unsendable, module = "axeyum", name = "Incremental")]
pub struct PyIncremental {
    solver: IncrementalBvSolver,
    epoch: u64,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyIncremental {
    /// Creates a warm solver bound to `arena`.
    #[new]
    #[pyo3(signature = (arena, config = None))]
    fn new(arena: PyRef<'_, Arena>, config: Option<&Config>) -> Self {
        let config: SolverConfig = Config::resolve(config);
        Self {
            solver: IncrementalBvSolver::with_config(config),
            epoch: arena.epoch,
        }
    }

    /// The arena epoch this solver is bound to.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Adds an assertion at the current scope.
    fn assert_(&mut self, arena: PyRef<'_, Arena>, term: Term) -> PyResult<()> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let id = term.resolve(self.epoch)?;
        self.solver
            .assert(&arena.arena, id)
            .map_err(|error| map_solver_error(&error))
    }

    /// Opens a new scope.
    fn push(&mut self) -> PyResult<()> {
        self.solver.push().map_err(|error| map_solver_error(&error))
    }

    /// Closes the innermost scope. Returns `False` at the base frame — that is
    /// the Rust contract and it is NOT an error.
    fn pop(&mut self) -> bool {
        self.solver.pop()
    }

    /// The current scope depth (`0` at the base frame).
    #[getter]
    fn scope_depth(&self) -> usize {
        self.solver.scope_depth()
    }

    /// Decides the current assertion stack.
    fn check(&mut self, py: Python<'_>, arena: PyRef<'_, Arena>) -> PyResult<PyCheckResult> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let solver = &mut self.solver;
        let subject: &axeyum_ir::TermArena = &arena.arena;
        let result = py
            .detach(move || solver.check(subject))
            .map_err(|error| map_solver_error(&error))?;
        Ok(PyCheckResult::build(self.epoch, &result))
    }

    /// Decides the current stack plus `assumptions`, without asserting them.
    fn check_assuming(
        &mut self,
        py: Python<'_>,
        arena: PyRef<'_, Arena>,
        assumptions: Vec<Term>,
    ) -> PyResult<PyCheckResult> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let ids = arena.resolve_terms(&assumptions)?;
        let solver = &mut self.solver;
        let subject: &axeyum_ir::TermArena = &arena.arena;
        let result = py
            .detach(move || solver.check_assuming(subject, &ids))
            .map_err(|error| map_solver_error(&error))?;
        Ok(PyCheckResult::build(self.epoch, &result))
    }

    /// Retained-encoding and timing counters.
    fn stats<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        let stats = self.solver.stats();
        let dict = PyDict::new(py);
        dict.set_item("word_rewrite_us", stats.word_rewrite.as_micros())?;
        dict.set_item("bit_blast_us", stats.bit_blast.as_micros())?;
        dict.set_item("cnf_encode_us", stats.cnf_encode.as_micros())?;
        dict.set_item("solve_us", stats.solve.as_micros())?;
        dict.set_item("model_lift_us", stats.model_lift.as_micros())?;
        dict.set_item("replay_us", stats.replay.as_micros())?;
        dict.set_item("root_encodings", stats.root_encodings)?;
        dict.set_item("checks", stats.checks)?;
        dict.set_item("aig_nodes", stats.aig_nodes)?;
        dict.set_item("cnf_variables", stats.cnf_variables)?;
        dict.set_item("cnf_clauses", stats.cnf_clauses)?;
        Ok(dict)
    }

    /// Retained CNF clause count.
    #[getter]
    fn encoded_clause_count(&self) -> usize {
        self.solver.encoded_clause_count()
    }

    /// Retained CNF variable count.
    #[getter]
    fn encoded_variable_count(&self) -> usize {
        self.solver.encoded_variable_count()
    }

    /// Retained AIG node count.
    #[getter]
    fn lowered_aig_node_count(&self) -> usize {
        self.solver.lowered_aig_node_count()
    }

    /// Turns on the replay-checked `sat` model cache.
    ///
    /// Only models that REPLAYED against the original terms are ever served
    /// from it; `unsat` without a source-bound proof is deliberately not
    /// cached at all.
    #[pyo3(signature = (max_entries = 128, max_values = 4096, max_bits = 65_536))]
    fn enable_replay_checked_sat_cache(
        &mut self,
        max_entries: usize,
        max_values: usize,
        max_bits: usize,
    ) -> PyResult<()> {
        self.solver
            .enable_replay_checked_sat_cache(ReplayCheckedSatCachePolicy::new(
                max_entries,
                max_values,
                max_bits,
            ))
            .map_err(|error| map_solver_error(&error))
    }

    /// Turns the replay-checked `sat` model cache off.
    fn disable_replay_checked_sat_cache(&mut self) {
        self.solver.disable_replay_checked_sat_cache();
    }

    /// Cache counters, including every DECLINE class.
    fn replay_checked_sat_cache_stats<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        let stats = self.solver.replay_checked_sat_cache_stats();
        let dict = PyDict::new(py);
        dict.set_item("hits", stats.hits)?;
        dict.set_item("misses", stats.misses)?;
        dict.set_item("insertions", stats.insertions)?;
        dict.set_item("evictions", stats.evictions)?;
        dict.set_item("replay_failures", stats.replay_failures)?;
        dict.set_item("declined_unsat", stats.declined_unsat)?;
        dict.set_item("declined_unknown", stats.declined_unknown)?;
        dict.set_item("declined_oversized_models", stats.declined_oversized_models)?;
        dict.set_item(
            "declined_non_scalar_models",
            stats.declined_non_scalar_models,
        )?;
        dict.set_item("entries", stats.entries)?;
        dict.set_item("model_values", stats.model_values)?;
        dict.set_item("model_bits", stats.model_bits)?;
        Ok(dict)
    }

    fn __repr__(&self) -> String {
        format!(
            "Incremental(epoch={}, scope_depth={}, clauses={})",
            self.epoch,
            self.solver.scope_depth(),
            self.solver.encoded_clause_count()
        )
    }
}

/// The capability matrix, as Markdown. Read-only data, not a log.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
pub fn capabilities() -> String {
    axeyum_solver::capabilities::capability_matrix_markdown()
}

/// The parser/IR/solver/proof support matrix, as Markdown.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
pub fn support_matrix() -> String {
    axeyum_solver::support_matrix::support_matrix_markdown()
}

/// The trust ledger — which reductions are certified and which are trusted.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
pub fn trust_ledger() -> String {
    axeyum_solver::trust::trust_ledger_markdown()
}

/// Every trust-step label, in canonical order.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.solver")
)]
#[pyfunction]
pub fn trust_ids() -> Vec<&'static str> {
    axeyum_solver::trust::ALL_TRUST_IDS
        .iter()
        .map(|id| id.label())
        .collect()
}

/// Registers the solving surface on the `solver` submodule.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyCheckResult>()?;
    module.add_class::<PyRouteTrace>()?;
    module.add_class::<PyEvidenceCheck>()?;
    module.add_class::<PyEvidenceReport>()?;
    module.add_class::<PyProofOutcome>()?;
    module.add_class::<PyIncremental>()?;
    module.add_function(wrap_pyfunction!(solve, module)?)?;
    module.add_function(wrap_pyfunction!(check_auto_explained, module)?)?;
    module.add_function(wrap_pyfunction!(unsat_core, module)?)?;
    module.add_function(wrap_pyfunction!(solve_with_strategy, module)?)?;
    module.add_function(wrap_pyfunction!(solve_with_portfolio, module)?)?;
    module.add_function(wrap_pyfunction!(recommended_portfolio, module)?)?;
    module.add_function(wrap_pyfunction!(produce_evidence, module)?)?;
    module.add_function(wrap_pyfunction!(prove, module)?)?;
    module.add_function(wrap_pyfunction!(capabilities, module)?)?;
    module.add_function(wrap_pyfunction!(support_matrix, module)?)?;
    module.add_function(wrap_pyfunction!(trust_ledger, module)?)?;
    module.add_function(wrap_pyfunction!(trust_ids, module)?)?;
    Ok(())
}
