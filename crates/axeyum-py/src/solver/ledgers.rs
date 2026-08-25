//! The read-only solver ledgers (tier R), as STRUCTURED data.
//!
//! Every table here already had a Markdown renderer bound
//! ([`capabilities`](super::core::capabilities),
//! [`support_matrix`](super::core::support_matrix),
//! [`trust_ledger`](super::core::trust_ledger)). Markdown is a rendering, not a
//! record: a caller that wants "which capabilities are `checked` by an
//! *external* checker" had to parse a table, and a parser that silently matches
//! nothing looks exactly like a table with no such rows. So the same three
//! sources of truth — `capabilities::CAPABILITIES`,
//! `support_matrix::SUPPORT_MATRIX` and `trust::ALL_TRUST_IDS` — are also
//! projected as frozen records carrying **every** field of the Rust struct.
//!
//! Two distinctions this module refuses to collapse:
//!
//! * `Assurance` (is there a certificate?) and `CheckedBy` (who reads it?) are
//!   separate fields, because `checked` + `argument-only` and `checked` +
//!   `external-artifact-checker` are very different claims.
//! * A [`TrustStep`]'s per-run `certified` bit and `TrustId::is_certified()`
//!   answer different questions, so both are exposed and neither is derived
//!   from the other.

#![allow(
    // PyO3's calling convention hands `PyRef` guards and owned `Vec<Term>`
    // arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use std::time::Duration;

use axeyum_solver::capabilities::{Assurance, CAPABILITIES, Capability, CheckedBy};
use axeyum_solver::support_matrix::{
    IrStatus, ParserStatus, ProofStatus, SUPPORT_MATRIX, SolverStatus, SupportRow,
};
use axeyum_solver::trust::{ALL_TRUST_IDS, TrustId, TrustStep};
use axeyum_solver::{Capabilities, SatBvBackend, SolveStats, SolverBackend};
use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::ir::arena::Arena;
use crate::ir::types::Term;
use crate::solver::results::{Config, PyCheckResult, map_solver_error};

/// Every [`Assurance`] variant, in source order.
///
/// The labels are read off the enum rather than restated, so this list cannot
/// drift from `capabilities::Assurance::label`.
const ASSURANCE_VARIANTS: &[Assurance] = &[
    Assurance::Checked,
    Assurance::Validated,
    Assurance::SoundIncomplete,
    Assurance::Experimental,
];

/// Every [`CheckedBy`] variant, in source order.
const CHECKED_BY_VARIANTS: &[CheckedBy] = &[
    CheckedBy::ExternalChecker,
    CheckedBy::SelfChecker,
    CheckedBy::DifferentialOracle,
    CheckedBy::Argument,
];

/// Every [`ParserStatus`] variant, in source order.
const PARSER_STATUS_VARIANTS: &[ParserStatus] = &[
    ParserStatus::Accepted,
    ParserStatus::AcceptedIgnored,
    ParserStatus::AcceptedBounded,
    ParserStatus::Rejected,
];

/// Every [`IrStatus`] variant, in source order.
const IR_STATUS_VARIANTS: &[IrStatus] = &[
    IrStatus::Modeled,
    IrStatus::Partial,
    IrStatus::Lowered,
    IrStatus::Absent,
];

/// Every [`SolverStatus`] variant, in source order.
const SOLVER_STATUS_VARIANTS: &[SolverStatus] = &[
    SolverStatus::Decides,
    SolverStatus::UnsatSatUnknown,
    SolverStatus::SoundIncomplete,
    SolverStatus::Unsupported,
];

/// Every [`ProofStatus`] variant, in source order.
const PROOF_STATUS_VARIANTS: &[ProofStatus] = &[
    ProofStatus::Checked,
    ProofStatus::PartialTrust,
    ProofStatus::NoProof,
];

/// One row of the capability ledger (`capabilities::CAPABILITIES`).
///
/// Tier **R** — read-only data. Nothing here decides anything; it is what this
/// build says it can do and how much of that is checked.
#[pyclass(frozen, module = "axeyum", name = "Capability")]
pub struct PyCapability {
    area: &'static str,
    feature: &'static str,
    assurance: &'static str,
    checked_by: &'static str,
    evidence: &'static str,
    reference: &'static str,
}

#[pymethods]
impl PyCapability {
    /// The row identity: `"<area> | <feature>"`.
    ///
    /// The Rust `Capability` struct has no id field — `(area, feature)` is the
    /// composite key — and this is that pair rendered exactly as the first two
    /// cells of the Markdown row, so `f"| {cap.id} |"` is a substring of
    /// [`capabilities()`](axeyum.solver.capabilities).
    #[getter]
    fn id(&self) -> String {
        format!("{} | {}", self.area, self.feature)
    }

    /// The logic fragment / theory area (`"QF_BV"`, `"QF_FP"`, …).
    #[getter]
    fn area(&self) -> &'static str {
        self.area
    }

    /// The specific capability within the area.
    #[getter]
    fn feature(&self) -> &'static str {
        self.feature
    }

    /// How much to trust a result: `"checked"`, `"validated"`,
    /// `"sound, incomplete"` or `"experimental"`.
    #[getter]
    fn assurance(&self) -> &'static str {
        self.assurance
    }

    /// WHO reads the artifact — the axis `assurance` does not carry.
    ///
    /// `"external-artifact-checker"` is the only value that answers "can a
    /// third party check this without trusting us?"; `"differential-only"`
    /// tests the verdict and not our artifact, and `"argument-only"` means
    /// decided, not certified.
    #[getter]
    fn checked_by(&self) -> &'static str {
        self.checked_by
    }

    /// What backs a result — the checkable artifact or validation basis.
    #[getter]
    fn evidence(&self) -> &'static str {
        self.evidence
    }

    /// The governing architecture-decision record.
    #[getter]
    fn reference(&self) -> &'static str {
        self.reference
    }

    fn __repr__(&self) -> String {
        format!(
            "Capability(area={:?}, feature={:?}, assurance={:?}, checked_by={:?})",
            self.area, self.feature, self.assurance, self.checked_by
        )
    }
}

impl PyCapability {
    fn build(capability: &Capability) -> Self {
        Self {
            area: capability.area,
            feature: capability.feature,
            assurance: capability.assurance.label(),
            checked_by: capability.checked_by.label(),
            evidence: capability.evidence,
            reference: capability.reference,
        }
    }
}

/// One row of the four-axis support matrix (`support_matrix::SUPPORT_MATRIX`).
///
/// Tier **R**. The four axes are INDEPENDENT on purpose: "the parser accepts
/// it" is not "the solver decides it" and neither is "the `unsat` carries a
/// proof".
#[pyclass(frozen, module = "axeyum", name = "SupportRow")]
pub struct PySupportRow {
    fragment: &'static str,
    parser: &'static str,
    ir: &'static str,
    solver: &'static str,
    proof: &'static str,
    note: &'static str,
}

#[pymethods]
impl PySupportRow {
    /// The logic fragment / feature — the row key.
    #[getter]
    fn fragment(&self) -> &'static str {
        self.fragment
    }

    /// parser-accepts: `"accepted"`, `"accepted-but-ignored"`,
    /// `"accepted (bounded)"` or `"rejected"`.
    #[getter]
    fn parser(&self) -> &'static str {
        self.parser
    }

    /// IR-semantics: `"modeled"`, `"partial"`, `"lowered (no IR sort)"` or
    /// `"absent"`.
    #[getter]
    fn ir(&self) -> &'static str {
        self.ir
    }

    /// solver-decides: `"decides"`, `"unsat decided; sat→unknown"`,
    /// `"sound, incomplete (unknown-safe)"` or `"unsupported"`.
    ///
    /// `"unsat decided; sat→unknown"` is a first-class honest answer, not a
    /// weaker form of `"decides"`.
    #[getter]
    fn solver(&self) -> &'static str {
        self.solver
    }

    /// proof-supports: `"checked"`, `"partial-trust"` or `"none"`.
    #[getter]
    fn proof(&self) -> &'static str {
        self.proof
    }

    /// A short note grounding the four cells in real code paths.
    #[getter]
    fn note(&self) -> &'static str {
        self.note
    }

    fn __repr__(&self) -> String {
        format!(
            "SupportRow(fragment={:?}, parser={:?}, ir={:?}, solver={:?}, proof={:?})",
            self.fragment, self.parser, self.ir, self.solver, self.proof
        )
    }
}

impl PySupportRow {
    fn build(row: &SupportRow) -> Self {
        Self {
            fragment: row.fragment,
            parser: row.parser.label(),
            ir: row.ir.label(),
            solver: row.solver.label(),
            proof: row.proof.label(),
            note: row.note,
        }
    }
}

/// One reduction of the trust ledger.
///
/// Tier **R**. Mirrors `trust::TrustStep` (`id` + the per-run `certified`
/// bit) and carries the `TrustId` metadata alongside it.
///
/// **`certified` and `ledger_certified` are different questions.**
/// `ledger_certified` is `TrustId::is_certified()`: *every* result relying on
/// this reduction has an independent per-query checker today. `certified` is
/// what a particular run carried. For the static
/// [`trust_ledger_rows()`](axeyum.solver.trust_ledger_rows) they are equal by
/// construction; on an
/// [`EvidenceReport.trust_steps`](axeyum.solver.EvidenceReport) they can
/// differ, and reading the ledger bit as an answer about one `unsat` is the
/// mistake `TrustId::is_certified`'s own doc comment warns about.
#[pyclass(frozen, module = "axeyum", name = "TrustStep")]
pub struct PyTrustStep {
    id: &'static str,
    meaning: &'static str,
    pedantic_level: u8,
    certified: bool,
    ledger_certified: bool,
    reference: &'static str,
}

#[pymethods]
impl PyTrustStep {
    /// The reduction's stable label (`"bit-blast"`, `"farkas"`, …).
    #[getter]
    fn id(&self) -> &'static str {
        self.id
    }

    /// One-line meaning of the reduction.
    #[getter]
    fn meaning(&self) -> &'static str {
        self.meaning
    }

    /// cvc5-style grade: 0 = hard fail (unsound if wrong) … 10 = minor.
    #[getter]
    fn pedantic_level(&self) -> u8 {
        self.pedantic_level
    }

    /// Whether THIS row carried an independent certificate.
    #[getter]
    fn certified(&self) -> bool {
        self.certified
    }

    /// `TrustId::is_certified()` — whether every result relying on this
    /// reduction has a per-query checker. A `False` here is a trust hole.
    #[getter]
    fn ledger_certified(&self) -> bool {
        self.ledger_certified
    }

    /// The ledger status word, `"certified"` or `"trust hole"`.
    #[getter]
    fn status(&self) -> &'static str {
        if self.ledger_certified {
            "certified"
        } else {
            "trust hole"
        }
    }

    /// The governing architecture-decision record.
    #[getter]
    fn reference(&self) -> &'static str {
        self.reference
    }

    fn __repr__(&self) -> String {
        format!(
            "TrustStep(id={:?}, certified={}, ledger_certified={})",
            self.id, self.certified, self.ledger_certified
        )
    }
}

impl PyTrustStep {
    /// Projects a per-run [`TrustStep`].
    pub(crate) fn build(step: TrustStep) -> Self {
        Self::of(step.id, step.certified)
    }

    /// Projects a [`TrustId`] with an explicit `certified` bit.
    fn of(id: TrustId, certified: bool) -> Self {
        Self {
            id: id.label(),
            meaning: id.meaning(),
            pedantic_level: id.pedantic_level(),
            certified,
            ledger_certified: id.is_certified(),
            reference: id.reference(),
        }
    }
}

/// Layer-attributed measurements from one backend check (`backend::SolveStats`).
///
/// Tier **R** — telemetry is returned data, not a log. Every duration is
/// exposed BOTH as whole nanoseconds and as seconds: a benchmark that silently
/// rounds is worse than one that is awkward to read.
#[pyclass(frozen, module = "axeyum", name = "SolveStats")]
pub struct PySolveStats {
    translate: Duration,
    solve: Duration,
    model_lift: Duration,
    terms_translated: u64,
    assertion_count: u64,
    backend: Vec<(String, f64)>,
}

#[pymethods]
impl PySolveStats {
    /// Nanoseconds spent translating Axeyum terms to the backend form.
    #[getter]
    fn translate_ns(&self) -> u128 {
        self.translate.as_nanos()
    }

    /// Seconds spent translating, as a float (lossy — prefer `translate_ns`).
    #[getter]
    fn translate_seconds(&self) -> f64 {
        self.translate.as_secs_f64()
    }

    /// Nanoseconds spent inside the backend's check.
    #[getter]
    fn solve_ns(&self) -> u128 {
        self.solve.as_nanos()
    }

    /// Seconds spent solving, as a float (lossy — prefer `solve_ns`).
    #[getter]
    fn solve_seconds(&self) -> f64 {
        self.solve.as_secs_f64()
    }

    /// Nanoseconds spent lifting a backend model into Axeyum-owned values.
    #[getter]
    fn model_lift_ns(&self) -> u128 {
        self.model_lift.as_nanos()
    }

    /// Seconds spent lifting the model (lossy — prefer `model_lift_ns`).
    #[getter]
    fn model_lift_seconds(&self) -> f64 {
        self.model_lift.as_secs_f64()
    }

    /// Unique DAG nodes translated.
    #[getter]
    fn terms_translated(&self) -> u64 {
        self.terms_translated
    }

    /// Number of top-level assertions.
    #[getter]
    fn assertion_count(&self) -> u64 {
        self.assertion_count
    }

    /// Backend-reported `(name, value)` counters, in the backend's own order.
    ///
    /// Backend-specific and **not a contract** — for post-mortems. An empty
    /// list is a normal answer, not a missing one.
    #[getter]
    fn backend(&self) -> Vec<(String, f64)> {
        self.backend.clone()
    }

    fn __repr__(&self) -> String {
        format!(
            "SolveStats(translate_ns={}, solve_ns={}, model_lift_ns={}, \
             terms_translated={}, assertion_count={}, backend_counters={})",
            self.translate.as_nanos(),
            self.solve.as_nanos(),
            self.model_lift.as_nanos(),
            self.terms_translated,
            self.assertion_count,
            self.backend.len()
        )
    }
}

impl PySolveStats {
    fn build(stats: &SolveStats) -> Self {
        Self {
            translate: stats.translate,
            solve: stats.solve,
            model_lift: stats.model_lift,
            terms_translated: stats.terms_translated,
            assertion_count: stats.assertion_count,
            backend: stats.backend.clone(),
        }
    }
}

/// What a backend can do (`backend::Capabilities`).
///
/// Tier **R**. Not uniform across backends — this is the backend's own report,
/// not a promise about the stack.
#[pyclass(frozen, module = "axeyum", name = "BackendCapabilities")]
pub struct PyBackendCapabilities {
    name: String,
    produces_models: bool,
    complete: bool,
}

#[pymethods]
impl PyBackendCapabilities {
    /// Human-readable backend name and version.
    #[getter]
    fn name(&self) -> &str {
        &self.name
    }

    /// Whether `sat` results carry models.
    #[getter]
    fn produces_models(&self) -> bool {
        self.produces_models
    }

    /// Whether the backend is refutation-complete for the M0 fragment.
    ///
    /// `False` is honest, not broken: a model-finding-only engine reports it.
    #[getter]
    fn complete(&self) -> bool {
        self.complete
    }

    fn __repr__(&self) -> String {
        format!(
            "BackendCapabilities(name={:?}, produces_models={}, complete={})",
            self.name, self.produces_models, self.complete
        )
    }
}

impl PyBackendCapabilities {
    fn build(capabilities: &Capabilities) -> Self {
        Self {
            name: capabilities.name.clone(),
            produces_models: capabilities.produces_models,
            complete: capabilities.complete,
        }
    }
}

/// The pure-Rust `QF_BV` backend, monomorphized.
///
/// `SolverBackend` is a Rust trait and is deliberately NOT implementable from
/// Python; this is the concrete default backend, bound so that its
/// `capabilities()` and `last_stats()` are reachable. It is the only place the
/// stack reports [`SolveStats`](axeyum.solver.SolveStats): the SMT-LIB front
/// door returns an `SmtLibOutcome`, which carries no telemetry, and
/// [`Incremental.stats()`](axeyum.solver.Incremental) is a different
/// (retained-encoding) counter set.
#[pyclass(module = "axeyum", name = "SatBvBackend")]
pub struct PySatBvBackend {
    backend: SatBvBackend,
}

#[pymethods]
impl PySatBvBackend {
    /// Creates a fresh backend. It reports no stats until it has checked.
    #[new]
    fn new() -> Self {
        Self {
            backend: SatBvBackend::new(),
        }
    }

    /// What this backend can do.
    fn capabilities(&self) -> PyBackendCapabilities {
        PyBackendCapabilities::build(&self.backend.capabilities())
    }

    /// Decides the conjunction of `assertions`.
    ///
    /// `unknown` is a value here too. Constructs outside the scalar `QF_BV`
    /// fragment raise `AxeyumError` (the Rust `Unsupported`) — there is no
    /// oracle fallback on this backend.
    #[pyo3(signature = (arena, assertions, config = None))]
    fn check(
        &mut self,
        py: Python<'_>,
        arena: PyRef<'_, Arena>,
        assertions: Vec<Term>,
        config: Option<&Config>,
    ) -> PyResult<PyCheckResult> {
        let epoch = arena.epoch;
        let ids = arena.resolve_terms(&assertions)?;
        let config = Config::resolve(config);
        let backend = &mut self.backend;
        let subject: &axeyum_ir::TermArena = &arena.arena;
        let result = py
            .detach(move || backend.check(subject, &ids, &config))
            .map_err(|error| map_solver_error(&error))?;
        Ok(PyCheckResult::build(epoch, &result))
    }

    /// Measurements from the most recent [`check`](Self::check).
    ///
    /// `None` before the first check — a value, not an error, and NOT an empty
    /// `SolveStats` (which would read as "the check took no time").
    fn last_stats(&self) -> Option<PySolveStats> {
        self.backend.last_stats().map(PySolveStats::build)
    }

    fn __repr__(&self) -> String {
        format!(
            "SatBvBackend(name={:?}, has_stats={})",
            self.backend.capabilities().name,
            self.backend.last_stats().is_some()
        )
    }
}

/// The capability ledger as structured rows, in `CAPABILITIES` source order.
///
/// The same data [`capabilities()`](axeyum.solver.capabilities) renders as
/// Markdown, with `assurance` and `checked_by` as separate fields.
#[pyfunction]
pub fn capability_rows() -> Vec<PyCapability> {
    CAPABILITIES.iter().map(PyCapability::build).collect()
}

/// The four-axis support matrix as structured rows, in `SUPPORT_MATRIX` order.
#[pyfunction]
pub fn support_matrix_rows() -> Vec<PySupportRow> {
    SUPPORT_MATRIX.iter().map(PySupportRow::build).collect()
}

/// The trust ledger as structured rows, in `ALL_TRUST_IDS` canonical order.
///
/// Each row's `certified` is the LEDGER-wide `TrustId::is_certified()`, so it
/// equals `ledger_certified`. A per-run bit lives on
/// `EvidenceReport.trust_steps`.
#[pyfunction]
pub fn trust_ledger_rows() -> Vec<PyTrustStep> {
    ALL_TRUST_IDS
        .iter()
        .map(|&id| PyTrustStep::of(id, id.is_certified()))
        .collect()
}

/// Maps a variant list through its `label` function.
fn labels<T: Copy>(variants: &[T], label: fn(T) -> &'static str) -> Vec<&'static str> {
    variants.iter().map(|&variant| label(variant)).collect()
}

/// Registers the read-only ledger surface on the `solver` submodule.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PyCapability>()?;
    module.add_class::<PySupportRow>()?;
    module.add_class::<PyTrustStep>()?;
    module.add_class::<PySolveStats>()?;
    module.add_class::<PyBackendCapabilities>()?;
    module.add_class::<PySatBvBackend>()?;
    module.add_function(wrap_pyfunction!(capability_rows, module)?)?;
    module.add_function(wrap_pyfunction!(support_matrix_rows, module)?)?;
    module.add_function(wrap_pyfunction!(trust_ledger_rows, module)?)?;
    module.add("ASSURANCES", labels(ASSURANCE_VARIANTS, Assurance::label))?;
    module.add("CHECKED_BY", labels(CHECKED_BY_VARIANTS, CheckedBy::label))?;
    module.add(
        "PARSER_STATUSES",
        labels(PARSER_STATUS_VARIANTS, ParserStatus::label),
    )?;
    module.add("IR_STATUSES", labels(IR_STATUS_VARIANTS, IrStatus::label))?;
    module.add(
        "SOLVER_STATUSES",
        labels(SOLVER_STATUS_VARIANTS, SolverStatus::label),
    )?;
    module.add(
        "PROOF_STATUSES",
        labels(PROOF_STATUS_VARIANTS, ProofStatus::label),
    )?;
    Ok(())
}
