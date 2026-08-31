//! `axeyum._native.producers` — tier P: untrusted, bounded proof producers.
//!
//! # What "untrusted" buys you
//!
//! Everything in this module *searches*. Nothing in it decides. A producer
//! returns a candidate proof term and the **same kernel** then re-checks it
//! through [`Kernel.add_declaration`](crate::kernel); a producer that returns a
//! wrong term produces a kernel rejection, never an admitted theorem. That is
//! why these functions can be reached from Python at all: no call here can
//! admit a fact, write a ledger, or change an axiom footprint.
//!
//! # `declined` is a value that arrives as an exception, and why
//!
//! CLAUDE.md's rule is that `unknown` and `declined` cross the language
//! boundary as *values*. The typed reason does: [`PyDeclineReason`] carries the
//! producer's own enum variant as `.kind` and its payload as `.detail`, and it
//! is never flattened to a string or a bool. It is *delivered* on
//! [`Declined`], an exception, because a decline has no candidate to return and
//! Python's alternative — `None` — would erase exactly the typed reason the
//! Rust enum exists to preserve. Catch [`Declined`] and read `.reason`; branch
//! on `.kind`, never on the message text.
//!
//! # Budgets are pinned constants, never keyword defaults
//!
//! [`MAX_BINDERS`](bounded_induction::MAX_BINDERS) is part of every settled
//! bounded-induction fact's reproduction contract: every
//! `mathlib-bounded-induction-family-*` manifest pins `max_binders: 8`, and
//! `scripts/check-autogenesis-bounded-induction-family.py` refuses a mismatch
//! **even when every `proof_sha256` is byte-identical**. Raising it to 12 was
//! reverted within the hour for that reason. So it is exported as a module
//! constant, and there is no argument through which Python can change it.
//!
//! # Handles
//!
//! Every `ExprId`/`NameId` here is the `axeyum.kernel` handle, carrying its
//! kernel's epoch, checked on every consuming call. A goal from another kernel
//! raises `EpochError` rather than silently denoting a different term.

use std::fs::File;
use std::io::{BufReader, Cursor};
use std::path::PathBuf;

use axeyum_lean_import::producers::{bounded_application, bounded_induction, modeq_family};
use axeyum_lean_import::{
    AxiomIdentity, CandidateTransportReceipt, DeclarationDependencyIdentity, DeclarationIdentity,
    ImportLimits, ImportReport,
    import_candidate_statement_ndjson as rust_import_candidate_statement_ndjson,
    import_statement_ndjson as rust_import_statement_ndjson, transport_checked_theorem_candidate,
};
use axeyum_lean_kernel::{
    Kernel, build_complex_prelude, build_creal_prelude, build_int_prelude, build_nat_prelude,
    build_rat_prelude,
};
use pyo3::create_exception;
use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyModule};

use crate::error::AxeyumError;
use crate::kernel::{PyExprId, PyKernel, PyNameId};
use crate::stub_types::PyBorrowedList;

create_exception!(
    axeyum,
    StatementImportError,
    AxeyumError,
    "A `lean4export` NDJSON stream failed the proof-isolated statement contract.\n\nThis is the gate that makes handing an untrusted producer a goal meaningful:\nit rejects every axiom, theorem, opaque and quotient declaration in the stream\nexcept the ones this import itself reconstructed, so the goal arrives with its\ndefinitional dependencies and no proof of itself. The Rust variant name is\ncarried as `.variant`."
);

create_exception!(
    axeyum,
    CandidateTransportError,
    AxeyumError,
    "A retrieved native theorem could not be checked into the imported goal kernel.\n\nThe typed Rust composition variant is carried as `.variant`; `.debug` retains the complete diagnostic. No partial target kernel is published on failure."
);

create_exception!(
    axeyum,
    Declined,
    AxeyumError,
    "A bounded producer declined to propose a candidate.\n\nThis is an ordinary outcome, not a failure: the producers are untrusted,\nbudgeted search, and exhausting a budget or meeting an unsupported goal shape\nis exactly what they are supposed to report. The typed reason is `.reason`, a\n`DeclineReason` with `.kind` and `.detail` -- branch on `.kind`, never on the\nmessage text."
);

// ---------------------------------------------------------------------------
// Decline reasons
// ---------------------------------------------------------------------------

/// Why a bounded producer declined, as its own typed enum variant.
///
/// `kind` is the Rust variant name verbatim (`"BinderBudgetExceeded"`,
/// `"NotEqualityGoal"`, …) and `detail` its payload, or `None` for a variant
/// that carries none. `producer` says which producer's vocabulary `kind` comes
/// from: the two enums overlap but are **not** the same type and do not have
/// the same variants.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "DeclineReason")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PyDeclineReason {
    /// `"bounded-induction"` or `"modeq-family"`.
    producer: &'static str,
    /// The Rust variant name.
    kind: String,
    /// The variant's payload, when it has one.
    detail: Option<String>,
    /// The Rust `Display` rendering, for a human reading a log.
    message: String,
}

impl PyDeclineReason {
    /// Projects `bounded_application::DeclineReason`.
    fn from_application(reason: &bounded_application::DeclineReason) -> Self {
        use bounded_application::DeclineReason as R;
        let kind = match reason {
            R::BinderBudgetExceeded => "BinderBudgetExceeded",
            R::NoUsableCandidates => "NoUsableCandidates",
            R::NoTypedApplication => "NoTypedApplication",
        };
        Self {
            producer: "bounded-application",
            kind: kind.to_owned(),
            detail: None,
            message: reason.to_string(),
        }
    }

    /// Projects `bounded_induction::DeclineReason`.
    fn from_bounded(reason: &bounded_induction::DeclineReason) -> Self {
        use bounded_induction::DeclineReason as R;
        let (kind, detail) = match reason {
            R::BinderBudgetExceeded => ("BinderBudgetExceeded", None),
            R::NotEqualityGoal => ("NotEqualityGoal", None),
            R::TerminalNotDefEqNoRewrite => ("TerminalNotDefEqNoRewrite", None),
            R::RequiredDeclarationUnavailable(detail) => {
                ("RequiredDeclarationUnavailable", Some(detail.clone()))
            }
            R::UnsupportedRecursorShape(detail) => {
                ("UnsupportedRecursorShape", Some(detail.clone()))
            }
        };
        Self {
            producer: "bounded-induction",
            kind: kind.to_owned(),
            detail,
            message: reason.to_string(),
        }
    }

    /// Projects `modeq_family::DeclineReason`.
    fn from_modeq(reason: &modeq_family::DeclineReason) -> Self {
        use modeq_family::DeclineReason as R;
        let (kind, detail) = match reason {
            R::BinderBudgetExceeded => ("BinderBudgetExceeded", None),
            R::RequiredDeclarationUnavailable(detail) => {
                ("RequiredDeclarationUnavailable", Some(detail.clone()))
            }
            R::UnsupportedRecursorShape(detail) => {
                ("UnsupportedRecursorShape", Some(detail.clone()))
            }
            R::UnsupportedIffShape(detail) => ("UnsupportedIffShape", Some(detail.clone())),
            R::TerminalNotClosed => ("TerminalNotClosed", None),
        };
        Self {
            producer: "modeq-family",
            kind: kind.to_owned(),
            detail,
            message: reason.to_string(),
        }
    }

    /// Builds the `Declined` exception carrying `self` as `.reason`.
    fn into_declined(self, py: Python<'_>) -> PyErr {
        let raised = Declined::new_err(format!("{} declined: {}", self.producer, self.message));
        match Py::new(py, self) {
            Ok(reason) => {
                if raised.value(py).setattr("reason", reason).is_err() {
                    return raised;
                }
                raised
            }
            Err(_) => raised,
        }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyDeclineReason {
    /// Which producer's vocabulary `kind` belongs to.
    #[getter]
    fn producer(&self) -> &'static str {
        self.producer
    }

    /// The Rust variant name, verbatim. Branch on this, never on the message.
    #[getter]
    fn kind(&self) -> &str {
        &self.kind
    }

    /// The variant's payload, or `None` for a variant that carries none.
    #[getter]
    fn detail(&self) -> Option<&str> {
        self.detail.as_deref()
    }

    /// The Rust `Display` rendering.
    #[getter]
    fn message(&self) -> &str {
        &self.message
    }

    fn __str__(&self) -> &str {
        &self.message
    }

    fn __repr__(&self) -> String {
        format!(
            "DeclineReason(producer={:?}, kind={:?}, detail={:?})",
            self.producer, self.kind, self.detail
        )
    }

    // `&Bound<'_, PyAny>`, not `&Self`: `__eq__` must accept ANY object.
    // Typed as `&Self` it raises TypeError on a mismatch, where Python expects
    // `False`, and the derived stub then declares `__eq__(self, other: Self)`,
    // which mypy rejects as a Liskov violation against `object.__eq__` -- the
    // stub package fails to BUILD, so `stubtest` compares nothing at all.
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other.cast::<Self>().is_ok_and(|other| self == other.get())
    }

    fn __hash__(&self) -> u64 {
        let mut hash = 0xcbf2_9ce4_8422_2325_u64;
        for byte in self
            .producer
            .as_bytes()
            .iter()
            .chain(self.kind.as_bytes())
            .chain(self.detail.as_deref().unwrap_or("\0").as_bytes())
        {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
        hash
    }
}

// ---------------------------------------------------------------------------
// Candidates
// ---------------------------------------------------------------------------

/// A bounded-induction candidate: a proposed proof term plus the search shape
/// that produced it.
///
/// `inductions_used == 0` means the goal closed by plain reflexivity. Nothing
/// here is checked: `proof` is untrusted until `Kernel.add_declaration` accepts
/// it as the value of a theorem whose type is the goal.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "Candidate")]
#[derive(Debug, Clone, Copy)]
pub struct PyCandidate {
    /// The proposed proof term, stamped with the producing kernel's epoch.
    proof: PyExprId,
    /// Leading `Pi` binders peeled, out of `MAX_BINDERS`.
    binders_used: usize,
    /// Structural inductions performed, out of `MAX_INDUCTIONS`.
    inductions_used: usize,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyCandidate {
    /// The proposed proof term. Untrusted until the kernel re-checks it.
    #[getter]
    fn proof(&self) -> PyExprId {
        self.proof
    }

    /// Leading `Pi` binders peeled, out of `MAX_BINDERS`.
    #[getter]
    fn binders_used(&self) -> usize {
        self.binders_used
    }

    /// Structural inductions performed, out of `MAX_INDUCTIONS`.
    #[getter]
    fn inductions_used(&self) -> usize {
        self.inductions_used
    }

    fn __repr__(&self) -> String {
        format!(
            "Candidate(binders_used={}, inductions_used={})",
            self.binders_used, self.inductions_used
        )
    }
}

/// A bounded-application candidate over an explicit retrieved declaration set.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "ApplicationCandidate"
)]
#[derive(Debug, Clone, Copy)]
pub struct PyApplicationCandidate {
    proof: PyExprId,
    binders_used: usize,
    application_depth: usize,
    terms_considered: usize,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyApplicationCandidate {
    /// Proposed proof term, untrusted until kernel admission.
    #[getter]
    fn proof(&self) -> PyExprId {
        self.proof
    }

    /// Leading goal binders introduced by the search.
    #[getter]
    fn binders_used(&self) -> usize {
        self.binders_used
    }

    /// Application-closure rounds consumed.
    #[getter]
    fn application_depth(&self) -> usize {
        self.application_depth
    }

    /// Distinct terms present when the proof was found.
    #[getter]
    fn terms_considered(&self) -> usize {
        self.terms_considered
    }

    fn __repr__(&self) -> String {
        format!(
            "ApplicationCandidate(binders_used={}, application_depth={}, terms_considered={})",
            self.binders_used, self.application_depth, self.terms_considered
        )
    }
}

/// A `ModEq`-family candidate: a proposed proof term plus the binder depth the
/// search reached.
///
/// Deliberately **not** the same class as [`PyCandidate`]. The two producers
/// measure different quantities against different budgets, and a single class
/// with `inductions_used = None` would make "this producer performs no
/// inductions" indistinguishable from "nobody measured".
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "ModEqCandidate"
)]
#[derive(Debug, Clone, Copy)]
pub struct PyModEqCandidate {
    /// The proposed proof term, stamped with the producing kernel's epoch.
    proof: PyExprId,
    /// Leading `Pi` binders peeled, out of `MODEQ_MAX_BINDERS`.
    binders_used: usize,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyModEqCandidate {
    /// The proposed proof term. Untrusted until the kernel re-checks it.
    #[getter]
    fn proof(&self) -> PyExprId {
        self.proof
    }

    /// Leading `Pi` binders peeled, out of `MODEQ_MAX_BINDERS`.
    #[getter]
    fn binders_used(&self) -> usize {
        self.binders_used
    }

    fn __repr__(&self) -> String {
        format!("ModEqCandidate(binders_used={})", self.binders_used)
    }
}

// ---------------------------------------------------------------------------
// Circularity audit
// ---------------------------------------------------------------------------

/// The mechanical circularity/trust audit an admitted candidate must pass.
///
/// Computed **only** from `declaration_dependency_closure`, `axiom_footprint`
/// and `theorem_dependencies` — never from a doc comment, never from a
/// head-symbol text match on a rendered name. The three counts are exposed
/// individually and `passes()` is derived from them, so a caller can see *why*
/// an audit failed rather than reading a bare `False`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "CircularityAudit"
)]
#[derive(Debug, Clone, Copy)]
pub struct PyCircularityAudit {
    /// Whether the candidate's transitive closure contains the target itself.
    target_dependency: bool,
    /// How many `Axiom`/`Opaque`/`Quotient` declarations the candidate reaches.
    axiom_footprint: usize,
    /// How many other already-proved theorems the candidate cites.
    theorem_dependencies: usize,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyCircularityAudit {
    /// Whether the candidate's transitive closure contains the target itself —
    /// the direct self-citation this guard exists for.
    #[getter]
    fn target_dependency(&self) -> bool {
        self.target_dependency
    }

    /// How many `Axiom`/`Opaque`/`Quotient` declarations the candidate reaches.
    ///
    /// Zero is this project's headline claim, so it is reported as a count and
    /// never collapsed into `passes()` alone.
    #[getter]
    fn axiom_footprint(&self) -> usize {
        self.axiom_footprint
    }

    /// How many other already-proved theorems the candidate cites.
    #[getter]
    fn theorem_dependencies(&self) -> usize {
        self.theorem_dependencies
    }

    /// No self-citation, no axiom/opaque/quotient reached, no borrowed theorem.
    fn passes(&self) -> bool {
        !self.target_dependency && self.axiom_footprint == 0 && self.theorem_dependencies == 0
    }

    fn __repr__(&self) -> String {
        // Rust's `bool` Display prints `true`/`false`; a Python repr must read
        // back as Python, so the two flags are spelled the Python way.
        format!(
            "CircularityAudit(target_dependency={}, axiom_footprint={}, theorem_dependencies={}, passes={})",
            if self.target_dependency {
                "True"
            } else {
                "False"
            },
            self.axiom_footprint,
            self.theorem_dependencies,
            if self.passes() { "True" } else { "False" }
        )
    }
}

// ---------------------------------------------------------------------------
// Import limits, report and identities
// ---------------------------------------------------------------------------

/// The `max_line_bytes` default, quoted from `ImportLimits::default()`.
///
/// A `const` rather than a literal in the `#[pyo3(signature)]` because the test
/// that pins it against Rust has to read the SAME value the signature uses. The
/// first version of that test wrote the literal twice and survived a mutation of
/// the signature -- a guard that cannot fail.
const DEFAULT_MAX_LINE_BYTES: usize = 16 * 1024 * 1024;

/// The `max_records` default, quoted from `ImportLimits::default()`.
const DEFAULT_MAX_RECORDS: usize = 2_000_000;

/// Resource limits applied before a stream can grow the kernel arenas without
/// bound.
///
/// The defaults are the Rust `ImportLimits::default()` values quoted:
/// `max_line_bytes = 16 * 1024 * 1024` (16 MiB) and `max_records = 2_000_000`.
/// `producers::tests::binding_defaults_match_rust` pins them, so a drift on
/// either side fails a test rather than silently changing what Python imports
/// under.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "ImportLimits")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PyImportLimits {
    /// The wrapped limits.
    inner: ImportLimits,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyImportLimits {
    /// Limits with the Rust defaults, or the given overrides.
    #[new]
    #[pyo3(signature = (max_line_bytes = DEFAULT_MAX_LINE_BYTES, max_records = DEFAULT_MAX_RECORDS))]
    fn new(max_line_bytes: usize, max_records: usize) -> Self {
        Self {
            inner: ImportLimits {
                max_line_bytes,
                max_records,
            },
        }
    }

    /// Maximum bytes in one NDJSON record, including its trailing newline.
    #[getter]
    fn max_line_bytes(&self) -> usize {
        self.inner.max_line_bytes
    }

    /// Maximum number of records, including the metadata record.
    #[getter]
    fn max_records(&self) -> usize {
        self.inner.max_records
    }

    fn __repr__(&self) -> String {
        format!(
            "ImportLimits(max_line_bytes={}, max_records={})",
            self.inner.max_line_bytes, self.inner.max_records
        )
    }

    // `&Bound<'_, PyAny>`, not `&Self`: `__eq__` must accept ANY object.
    // Typed as `&Self` it raises TypeError on a mismatch, where Python expects
    // `False`, and the derived stub then declares `__eq__(self, other: Self)`,
    // which mypy rejects as a Liskov violation against `object.__eq__` -- the
    // stub package fails to BUILD, so `stubtest` compares nothing at all.
    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other.cast::<Self>().is_ok_and(|other| self == other.get())
    }

    fn __hash__(&self) -> u64 {
        u64::try_from(self.inner.max_line_bytes)
            .unwrap_or(u64::MAX)
            .rotate_left(32)
            ^ u64::try_from(self.inner.max_records).unwrap_or(u64::MAX)
    }
}

/// One imported axiom bound to TL0.4-compatible name and type identities.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(frozen, skip_from_py_object, module = "axeyum", name = "AxiomIdentity")]
#[derive(Debug, Clone)]
pub struct PyAxiomIdentity {
    /// Exact displayed hierarchical declaration name.
    name: String,
    /// SHA-256 of the UTF-8 displayed name.
    name_sha256: String,
    /// SHA-256 of the rendered type.
    type_sha256: String,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyAxiomIdentity {
    /// Exact displayed hierarchical declaration name.
    #[getter]
    fn name(&self) -> &str {
        &self.name
    }

    /// SHA-256 of the UTF-8 displayed name.
    #[getter]
    fn name_sha256(&self) -> &str {
        &self.name_sha256
    }

    /// SHA-256 of `render_lean(declaration.ty())`.
    #[getter]
    fn type_sha256(&self) -> &str {
        &self.type_sha256
    }

    fn __repr__(&self) -> String {
        format!("AxiomIdentity(name={:?})", self.name)
    }
}

/// One direct dependency bound to the dependency's structural content.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "DeclarationDependency"
)]
#[derive(Debug, Clone)]
pub struct PyDeclarationDependency {
    /// Exact displayed hierarchical dependency name.
    name: String,
    /// Structural content SHA-256 of the admitted dependency declaration.
    content_sha256: String,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyDeclarationDependency {
    /// Exact displayed hierarchical dependency name.
    #[getter]
    fn name(&self) -> &str {
        &self.name
    }

    /// Structural content SHA-256 of the admitted dependency declaration.
    #[getter]
    fn content_sha256(&self) -> &str {
        &self.content_sha256
    }

    fn __repr__(&self) -> String {
        format!("DeclarationDependency(name={:?})", self.name)
    }
}

/// Canonical identity for one independently admitted declaration.
///
/// `content_sha256` is what a family manifest's `target_content_sha256` pins:
/// it is arena-independent, so two imports of the same bytes agree.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(frozen, module = "axeyum", name = "DeclarationIdentity")]
#[derive(Debug)]
pub struct PyDeclarationIdentity {
    /// Exact displayed hierarchical declaration name.
    name: String,
    /// Stable declaration variant (`"definition"`, `"inductive"`, …).
    kind: &'static str,
    /// Domain-separated structural SHA-256 of the complete checked content.
    content_sha256: String,
    /// Domain-separated SHA-256 of the sorted direct-dependency bindings.
    dependency_sha256: String,
    /// Sorted, deduplicated direct-dependency bindings.
    dependencies: Vec<Py<PyDeclarationDependency>>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyDeclarationIdentity {
    /// Exact displayed hierarchical declaration name.
    #[getter]
    fn name(&self) -> &str {
        &self.name
    }

    /// Stable declaration variant.
    #[getter]
    fn kind(&self) -> &'static str {
        self.kind
    }

    /// Domain-separated structural SHA-256 of the complete checked content.
    #[getter]
    fn content_sha256(&self) -> &str {
        &self.content_sha256
    }

    /// Domain-separated SHA-256 of the sorted direct-dependency bindings.
    #[getter]
    fn dependency_sha256(&self) -> &str {
        &self.dependency_sha256
    }

    /// Sorted, deduplicated direct-dependency bindings.
    #[getter]
    fn dependencies(&self, py: Python<'_>) -> Vec<Py<PyDeclarationDependency>> {
        self.dependencies
            .iter()
            .map(|row| row.clone_ref(py))
            .collect()
    }

    fn __repr__(&self) -> String {
        format!(
            "DeclarationIdentity(name={:?}, kind={:?})",
            self.name, self.kind
        )
    }
}

/// Counts and provenance for a successfully admitted stream.
///
/// `substituted_theorems` is the field that tells "our own re-derivation" apart
/// from "an admitted trusted declaration": every name in it still reports
/// `kind == "theorem"` in `declaration_identities`, which is structurally true
/// and would otherwise be indistinguishable.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(frozen, module = "axeyum", name = "ImportReport")]
#[derive(Debug)]
pub struct PyImportReport {
    /// Export-format version from the first record.
    format_version: String,
    /// Official Lean version recorded by the exporter.
    lean_version: String,
    /// Official Lean source hash recorded by the exporter.
    lean_githash: String,
    /// Exporter version recorded by the stream.
    exporter_version: String,
    /// Number of non-anonymous exported names.
    names: usize,
    /// Number of nonzero exported universe-level records.
    levels: usize,
    /// Number of exported expression records.
    expressions: usize,
    /// Number of exported declaration records.
    declaration_records: usize,
    /// Number of kernel declarations admitted.
    admitted_declarations: usize,
    /// Imported axiom names.
    axioms: Vec<String>,
    /// Identity schema for the two manifests below.
    identity_version: String,
    /// Imported axiom name/type identities.
    axiom_identities: Vec<Py<PyAxiomIdentity>>,
    /// Canonical identities for every admitted declaration.
    declaration_identities: Vec<Py<PyDeclarationIdentity>>,
    /// Theorems this crate reconstructed and re-checked itself.
    substituted_theorems: Vec<String>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyImportReport {
    /// Export-format version from the first record.
    #[getter]
    fn format_version(&self) -> &str {
        &self.format_version
    }

    /// Official Lean version recorded by the exporter.
    #[getter]
    fn lean_version(&self) -> &str {
        &self.lean_version
    }

    /// Official Lean source hash recorded by the exporter.
    #[getter]
    fn lean_githash(&self) -> &str {
        &self.lean_githash
    }

    /// Exporter version recorded by the stream.
    #[getter]
    fn exporter_version(&self) -> &str {
        &self.exporter_version
    }

    /// Number of non-anonymous exported names.
    #[getter]
    fn names(&self) -> usize {
        self.names
    }

    /// Number of nonzero exported universe-level records.
    #[getter]
    fn levels(&self) -> usize {
        self.levels
    }

    /// Number of exported expression records.
    #[getter]
    fn expressions(&self) -> usize {
        self.expressions
    }

    /// Number of exported declaration records; an inductive group is one.
    #[getter]
    fn declaration_records(&self) -> usize {
        self.declaration_records
    }

    /// Number of kernel declarations admitted.
    #[getter]
    fn admitted_declarations(&self) -> usize {
        self.admitted_declarations
    }

    /// Imported axiom names. Their types were checked; their propositions
    /// remain assumptions until discharged separately.
    #[getter]
    fn axioms(&self) -> PyBorrowedList<'_, String> {
        PyBorrowedList(&self.axioms)
    }

    /// Identity schema for the two manifests below.
    #[getter]
    fn identity_version(&self) -> &str {
        &self.identity_version
    }

    /// Imported axiom name/type identities.
    #[getter]
    fn axiom_identities(&self, py: Python<'_>) -> Vec<Py<PyAxiomIdentity>> {
        self.axiom_identities
            .iter()
            .map(|row| row.clone_ref(py))
            .collect()
    }

    /// Canonical identities for every admitted declaration.
    #[getter]
    fn declaration_identities(&self, py: Python<'_>) -> Vec<Py<PyDeclarationIdentity>> {
        self.declaration_identities
            .iter()
            .map(|row| row.clone_ref(py))
            .collect()
    }

    /// Theorems this crate reconstructed and independently re-checked itself,
    /// in place of the untrusted wire-supplied type/value.
    #[getter]
    fn substituted_theorems(&self) -> PyBorrowedList<'_, String> {
        PyBorrowedList(&self.substituted_theorems)
    }

    fn __repr__(&self) -> String {
        format!(
            "ImportReport(lean_version={:?}, admitted_declarations={}, axioms={})",
            self.lean_version,
            self.admitted_declarations,
            self.axioms.len()
        )
    }
}

/// Projects a Rust `ImportReport` onto its Python view.
fn build_report(py: Python<'_>, report: &ImportReport) -> PyResult<Py<PyImportReport>> {
    let axiom_identities = report
        .axiom_identities
        .iter()
        .map(|row: &AxiomIdentity| {
            Py::new(
                py,
                PyAxiomIdentity {
                    name: row.name.clone(),
                    name_sha256: row.name_sha256.clone(),
                    type_sha256: row.type_sha256.clone(),
                },
            )
        })
        .collect::<PyResult<Vec<_>>>()?;
    let declaration_identities = report
        .declaration_identities
        .iter()
        .map(|row: &DeclarationIdentity| {
            let dependencies = row
                .dependencies
                .iter()
                .map(|dep: &DeclarationDependencyIdentity| {
                    Py::new(
                        py,
                        PyDeclarationDependency {
                            name: dep.name.clone(),
                            content_sha256: dep.content_sha256.clone(),
                        },
                    )
                })
                .collect::<PyResult<Vec<_>>>()?;
            Py::new(
                py,
                PyDeclarationIdentity {
                    name: row.name.clone(),
                    kind: row.kind.as_str(),
                    content_sha256: row.content_sha256.clone(),
                    dependency_sha256: row.dependency_sha256.clone(),
                    dependencies,
                },
            )
        })
        .collect::<PyResult<Vec<_>>>()?;
    Py::new(
        py,
        PyImportReport {
            format_version: report.format_version.clone(),
            lean_version: report.lean_version.clone(),
            lean_githash: report.lean_githash.clone(),
            exporter_version: report.exporter_version.clone(),
            names: report.names,
            levels: report.levels,
            expressions: report.expressions,
            declaration_records: report.declaration_records,
            admitted_declarations: report.admitted_declarations,
            axioms: report.axioms.clone(),
            identity_version: report.identity_version.to_owned(),
            axiom_identities,
            declaration_identities,
            substituted_theorems: report.substituted_theorems.clone(),
        },
    )
}

// ---------------------------------------------------------------------------
// Statement import
// ---------------------------------------------------------------------------

/// One proof-isolated proposition imported as the value of a transparent
/// `definition : Prop`.
///
/// The kernel, the goal and the target name are one unit: the handles are
/// indices into *this* import's kernel and mean nothing anywhere else. So
/// `kernel()` returns the **same** `Kernel` object every time — a producer
/// mutates it (interning the proof term, admitting the candidate) and the goal
/// stays valid across that. Getting a fresh copy each call would silently
/// invalidate every handle already handed out.
///
/// The Rust `into_parts` is deliberately not bound: it consumes the import, and
/// the four non-consuming accessors give the same values.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(module = "axeyum", name = "StatementImport")]
pub struct PyStatementImport {
    /// The independently checked environment, under its own fresh epoch.
    kernel: Py<PyKernel>,
    /// The completed import inventory.
    report: Py<PyImportReport>,
    /// The target definition name, stamped with the kernel's epoch.
    target_name: PyNameId,
    /// The checked proposition, stamped with the kernel's epoch.
    goal: PyExprId,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyStatementImport {
    // ORDER MATTERS HERE, and only here. `kernel()` is the last accessor
    // deliberately: the generated stub imports the sibling module as
    // `from axeyum._native import kernel`, and inside a class body a member
    // named `kernel` shadows that import for every annotation written AFTER it.
    // With this method first, `goal(self) -> kernel.ExprId` two lines down
    // resolves `kernel` to this method and mypy refuses to build the stub
    // package at all -- so `stubtest` compares nothing and exits reporting a
    // build error rather than a stub problem. Measured 2026-08-24.

    /// The checked proposition to hand to an untrusted proof producer.
    fn goal(&self) -> PyExprId {
        self.goal
    }

    /// The target definition name in this import's kernel.
    fn target_name(&self) -> PyNameId {
        self.target_name
    }

    /// The completed import inventory and canonical declaration identities.
    fn report(&self, py: Python<'_>) -> Py<PyImportReport> {
        self.report.clone_ref(py)
    }

    /// The independently checked environment holding the goal's definitional
    /// dependencies and no proof of the goal.
    ///
    /// The same object on every call: handles stay valid across a producer's
    /// mutations.
    fn kernel(&self, py: Python<'_>) -> Py<PyKernel> {
        self.kernel.clone_ref(py)
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        let epoch = self.kernel.borrow(py).epoch_value();
        format!("StatementImport(kernel_epoch={epoch})")
    }
}

/// Checked evidence that one retrieved native theorem is executable in an
/// imported goal kernel.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.producers")
)]
#[pyclass(
    frozen,
    skip_from_py_object,
    module = "axeyum",
    name = "CandidateTransport"
)]
pub struct PyCandidateTransport {
    candidate: PyNameId,
    disposition: &'static str,
    source_closure_size: usize,
    added_theorems: usize,
    added_definitions: usize,
    receipt_sha256: Option<String>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyCandidateTransport {
    /// Candidate handle belonging to the statement import's same kernel.
    #[getter]
    fn candidate(&self) -> PyNameId {
        self.candidate
    }

    /// `"added"` for checked composition or `"reused"` for checked reuse.
    #[getter]
    fn disposition(&self) -> &'static str {
        self.disposition
    }

    /// Root-selected native declaration closure size (zero for reuse).
    #[getter]
    fn source_closure_size(&self) -> usize {
        self.source_closure_size
    }

    /// Theorems newly admitted by this transport.
    #[getter]
    fn added_theorems(&self) -> usize {
        self.added_theorems
    }

    /// Definitions newly admitted by this transport.
    #[getter]
    fn added_definitions(&self) -> usize {
        self.added_definitions
    }

    /// Digest of an added composition receipt; reuse has no aggregate receipt.
    #[getter]
    fn receipt_sha256(&self) -> Option<&str> {
        self.receipt_sha256.as_deref()
    }

    fn __repr__(&self) -> String {
        format!(
            "CandidateTransport(disposition={:?}, source_closure_size={}, added_theorems={}, added_definitions={})",
            self.disposition, self.source_closure_size, self.added_theorems, self.added_definitions,
        )
    }
}

/// Where the NDJSON bytes come from.
enum Source {
    /// A filesystem path.
    Path(PathBuf),
    /// An in-memory stream.
    Bytes(Vec<u8>),
}

/// Resolves the `source` argument, checking `bytes` **before** `PathBuf`.
///
/// The order matters: `PyO3` extracts a `PathBuf` from `bytes` on Unix, so
/// trying the path first would turn a byte stream into a nonsensical filename.
fn resolve_source(source: &Bound<'_, PyAny>) -> PyResult<Source> {
    if source.is_instance_of::<PyBytes>() {
        return Ok(Source::Bytes(source.extract::<Vec<u8>>()?));
    }
    if let Ok(path) = source.extract::<PathBuf>() {
        return Ok(Source::Path(path));
    }
    Err(PyTypeError::new_err(
        "source must be a path (str or os.PathLike) or the NDJSON bytes themselves",
    ))
}

/// Projects a Rust `StatementImportError` onto the Python exception.
fn statement_import_error(
    py: Python<'_>,
    error: &axeyum_lean_import::StatementImportError,
) -> PyErr {
    let debug = format!("{error:?}");
    let variant = debug
        .split(|c: char| !c.is_alphanumeric() && c != '_')
        .find(|part| !part.is_empty())
        .unwrap_or("Unknown")
        .to_owned();
    let raised = StatementImportError::new_err(error.to_string());
    let value = raised.value(py);
    if value.setattr("variant", &variant).is_err() || value.setattr("debug", &debug).is_err() {
        return raised;
    }
    raised
}

/// Imports one proof-isolated proposition from a `lean4export` NDJSON stream.
///
/// This is the front door for "hand an untrusted producer a goal". It rejects
/// every axiom, theorem, opaque and quotient declaration in the stream except
/// the ones this import itself reconstructed (`report.substituted_theorems`),
/// so the returned kernel can define the goal but cannot prove it.
///
/// `source` is a path (`str` / `os.PathLike`) or the NDJSON `bytes`. `limits`
/// of `None` uses the Rust `ImportLimits::default()`.
///
/// # Errors
///
/// Raises `TypeError` for a `source` that is neither, `OSError` if the file
/// cannot be opened, and `StatementImportError` if the stream fails the
/// proof-isolation contract.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.producers")
)]
#[pyfunction]
#[pyo3(signature = (source, limits, target))]
fn import_statement_ndjson(
    py: Python<'_>,
    source: &Bound<'_, PyAny>,
    limits: Option<PyImportLimits>,
    target: &str,
) -> PyResult<PyStatementImport> {
    let source = resolve_source(source)?;
    let limits = limits.map_or_else(ImportLimits::default, |limits| limits.inner);
    let completed = match source {
        Source::Path(path) => {
            let file = File::open(&path)?;
            py.detach(move || rust_import_statement_ndjson(BufReader::new(file), limits, target))
        }
        Source::Bytes(bytes) => py.detach(move || {
            rust_import_statement_ndjson(BufReader::new(Cursor::new(bytes)), limits, target)
        }),
    }
    .map_err(|error| statement_import_error(py, &error))?;
    wrap_statement_import(py, completed)
}

/// Imports a proof-free target plus an exact axiom-free theorem candidate set.
///
/// Unlike [`import_statement_ndjson`], this capsule may carry proof-bearing
/// declarations, but only those whose exact names occur in `candidates`; every
/// one is independently kernel-checked and must have an empty measured axiom
/// footprint. The target remains a transparent `definition : Prop`, never a
/// theorem. The bounded-application producer must still receive the same names
/// explicitly and cannot scan the returned environment.
///
/// `source` is a path (`str` / `os.PathLike`) or the NDJSON `bytes`. `limits`
/// of `None` uses the Rust `ImportLimits::default()`.
///
/// # Errors
///
/// Raises `TypeError` for an invalid source, `OSError` for an unreadable path,
/// and `StatementImportError` for any wire, target-isolation, candidate-identity
/// or axiom-footprint failure.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.producers")
)]
#[pyfunction]
#[pyo3(signature = (source, limits, target, candidates))]
fn import_candidate_statement_ndjson(
    py: Python<'_>,
    source: &Bound<'_, PyAny>,
    limits: Option<PyImportLimits>,
    target: &str,
    candidates: Vec<String>,
) -> PyResult<PyStatementImport> {
    let source = resolve_source(source)?;
    let limits = limits.map_or_else(ImportLimits::default, |limits| limits.inner);
    let completed = match source {
        Source::Path(path) => {
            let file = File::open(&path)?;
            py.detach(move || {
                rust_import_candidate_statement_ndjson(
                    BufReader::new(file),
                    limits,
                    target,
                    &candidates,
                )
            })
        }
        Source::Bytes(bytes) => py.detach(move || {
            rust_import_candidate_statement_ndjson(
                BufReader::new(Cursor::new(bytes)),
                limits,
                target,
                &candidates,
            )
        }),
    }
    .map_err(|error| statement_import_error(py, &error))?;
    wrap_statement_import(py, completed)
}

fn wrap_statement_import(
    py: Python<'_>,
    completed: axeyum_lean_import::CompletedStatementImport,
) -> PyResult<PyStatementImport> {
    let (kernel, report, target_name, goal) = completed.into_parts();
    let report = build_report(py, &report)?;
    let wrapper = PyKernel::from_kernel(kernel);
    let target_name = wrapper.wrap_name(target_name);
    let goal = wrapper.wrap_expr(goal);
    Ok(PyStatementImport {
        kernel: Py::new(py, wrapper)?,
        report,
        target_name,
        goal,
    })
}

/// Projects a checked theorem-composition failure without flattening its
/// stable Rust variant into the human message.
fn candidate_transport_error(
    py: Python<'_>,
    error: &axeyum_lean_import::CheckedTheoremCompositionError,
) -> PyErr {
    let debug = format!("{error:?}");
    let variant = debug
        .split(|c: char| !c.is_alphanumeric() && c != '_')
        .find(|part| !part.is_empty())
        .unwrap_or("Unknown")
        .to_owned();
    let raised = CandidateTransportError::new_err(error.to_string());
    let value = raised.value(py);
    if value.setattr("variant", &variant).is_err() || value.setattr("debug", &debug).is_err() {
        return raised;
    }
    raised
}

/// Build the independently owned native prelude that owns `candidate`.
fn native_candidate_source(candidate: &str) -> Result<Kernel, String> {
    let mut source = Kernel::new();
    let result = if candidate.starts_with("Nat.") {
        build_nat_prelude(&mut source).map(|_| ())
    } else if candidate.starts_with("Int.") {
        build_int_prelude(&mut source).map(|_| ())
    } else if candidate.starts_with("Rat.") {
        build_rat_prelude(&mut source).map(|_| ())
    } else if candidate.starts_with("CReal.") {
        build_creal_prelude(&mut source).map(|_| ())
    } else if candidate.starts_with("Complex.") {
        build_complex_prelude(&mut source).map(|_| ())
    } else {
        return Err(format!(
            "UnsupportedCandidateNamespace: no native prelude owns {candidate:?}"
        ));
    };
    result
        .map(|()| source)
        .map_err(|error| format!("NativePreludeBuildFailed: {error:?}"))
}

/// Check one retrieved native theorem into an imported goal's private kernel.
///
/// The candidate namespace deterministically selects the independently rebuilt
/// native prelude (`Nat`, `Int`, `Rat`, `CReal`, or `Complex`). Existing target
/// theorems are compatibility-checked; absent ones go through checked theorem
/// composition. The target proof remains absent, and no fact or operation
/// authority is granted. The statement import keeps the same Python `Kernel`
/// object and epoch because composition clones and only extends its arenas, so
/// all previously issued goal/name handles remain valid.
///
/// # Errors
///
/// Raises `CandidateTransportError` with `.variant` and `.debug` when the
/// namespace is unsupported or the exact source root cannot be safely reused
/// or composed. A failure never changes the statement import's kernel.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.producers")
)]
#[pyfunction]
fn transport_native_candidate(
    py: Python<'_>,
    statement: &PyStatementImport,
    candidate: &str,
) -> PyResult<PyCandidateTransport> {
    let source_candidate = candidate.to_owned();
    let source = py
        .detach(move || native_candidate_source(&source_candidate))
        .map_err(|message| {
            let raised = CandidateTransportError::new_err(message.clone());
            let value = raised.value(py);
            let variant = message.split(':').next().unwrap_or("Unknown");
            if value.setattr("variant", variant).is_ok() {
                let _ = value.setattr("debug", &message);
            }
            raised
        })?;
    let target = statement.kernel.borrow(py).inner().clone();
    let transport_candidate = candidate.to_owned();
    let completed = py
        .detach(move || transport_checked_theorem_candidate(&source, &target, &transport_candidate))
        .map_err(|error| candidate_transport_error(py, &error))?;
    let (completed_kernel, candidate_id, receipt) = completed.into_parts();
    let (disposition, source_closure_size, added_theorems, added_definitions, receipt_sha256) =
        match receipt {
            CandidateTransportReceipt::Added(receipt) => (
                "added",
                receipt.source_closure.len(),
                receipt.added_theorems.len(),
                receipt.added_definitions.len(),
                Some(receipt.receipt_sha256),
            ),
            CandidateTransportReceipt::Reused(_) => ("reused", 0, 0, 0, None),
        };
    let mut target = statement.kernel.borrow_mut(py);
    *target.inner_mut() = completed_kernel;
    Ok(PyCandidateTransport {
        candidate: target.wrap_name(candidate_id),
        disposition,
        source_closure_size,
        added_theorems,
        added_definitions,
        receipt_sha256,
    })
}

// ---------------------------------------------------------------------------
// The producers
// ---------------------------------------------------------------------------

/// Proposes a bounded structural-induction proof of `goal`.
///
/// `Eq.refl`, and where that is stuck, a bounded induction over a discovered
/// zero/succ-shaped binder plus congruence rewrites driven by the induction
/// hypothesis. Target-agnostic: it never dispatches on a declaration name or a
/// fact id, and every structural fact it uses is discovered from `kernel`'s own
/// declarations.
///
/// The returned proof is **untrusted**. Admit it with
/// `Kernel.add_declaration(Declaration.theorem(name, [], goal, candidate.proof))`
/// and read `Kernel.axiom_footprint` afterwards; the kernel, not this call, is
/// what decides.
///
/// # Errors
///
/// Raises `EpochError` if `goal` was interned by another kernel, and `Declined`
/// carrying a typed `.reason` when the bounded search does not close the goal.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.producers")
)]
#[pyfunction]
fn propose_bounded_induction(
    py: Python<'_>,
    mut kernel: PyRefMut<'_, PyKernel>,
    goal: PyExprId,
) -> PyResult<PyCandidate> {
    let id = kernel.expr_of(goal)?;
    let inner = kernel.inner_mut();
    let proposed = py.detach(move || bounded_induction::propose_bounded_induction(inner, id));
    match proposed {
        Ok(candidate) => {
            let proof = kernel.wrap_expr(candidate.proof);
            Ok(PyCandidate {
                proof,
                binders_used: candidate.binders_used,
                inductions_used: candidate.inductions_used,
            })
        }
        Err(reason) => Err(PyDeclineReason::from_bounded(&reason).into_declined(py)),
    }
}

/// Proposes bounded induction with exact retrieved declarations available for
/// typed equality rewriting in the current induction scope.
///
/// `declarations` is an explicit retrieval boundary, not proof authority. The
/// producer preserves caller order, ignores unusable candidates, applies fixed
/// Rust-side budgets, and returns an untrusted term for same-kernel admission.
///
/// # Errors
///
/// Raises `EpochError` for a foreign goal/name handle and `Declined` with the
/// bounded-induction reason when the combined grammar cannot close the goal.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.producers")
)]
#[pyfunction]
fn propose_bounded_induction_with_rewrites(
    py: Python<'_>,
    mut kernel: PyRefMut<'_, PyKernel>,
    goal: PyExprId,
    declarations: Vec<PyNameId>,
) -> PyResult<PyCandidate> {
    let goal = kernel.expr_of(goal)?;
    let declarations = declarations
        .into_iter()
        .map(|name| kernel.name_of(name))
        .collect::<PyResult<Vec<_>>>()?;
    let inner = kernel.inner_mut();
    let proposed = py.detach(move || {
        bounded_induction::propose_bounded_induction_with_rewrites(inner, goal, &declarations)
    });
    match proposed {
        Ok(candidate) => Ok(PyCandidate {
            proof: kernel.wrap_expr(candidate.proof),
            binders_used: candidate.binders_used,
            inductions_used: candidate.inductions_used,
        }),
        Err(reason) => Err(PyDeclineReason::from_bounded(&reason).into_declined(py)),
    }
}

/// Proposes a bounded type-directed application proof from exact declarations.
///
/// `declarations` is the retrieval boundary: the producer does not scan the
/// environment. Do not include the target theorem. The returned proof remains
/// untrusted until the same kernel admits it as a theorem of `goal`.
///
/// # Errors
///
/// Raises `EpochError` for a foreign goal/name handle and `Declined` with a
/// typed bounded-application reason when the fixed search budget finds no term.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.producers")
)]
#[pyfunction]
fn propose_bounded_application(
    py: Python<'_>,
    mut kernel: PyRefMut<'_, PyKernel>,
    goal: PyExprId,
    declarations: Vec<PyNameId>,
) -> PyResult<PyApplicationCandidate> {
    let goal = kernel.expr_of(goal)?;
    let declarations = declarations
        .into_iter()
        .map(|name| kernel.name_of(name))
        .collect::<PyResult<Vec<_>>>()?;
    let inner = kernel.inner_mut();
    let proposed = py.detach(move || {
        bounded_application::propose_bounded_application(inner, goal, &declarations)
    });
    match proposed {
        Ok(candidate) => Ok(PyApplicationCandidate {
            proof: kernel.wrap_expr(candidate.proof),
            binders_used: candidate.binders_used,
            application_depth: candidate.application_depth,
            terms_considered: candidate.terms_considered,
        }),
        Err(reason) => Err(PyDeclineReason::from_application(&reason).into_declined(py)),
    }
}

/// Proposes a bounded `Eq`/`Iff`-combinator proof of `goal`.
///
/// The `ModEq` definitional-equivalence family: `ModEq n a b` unfolds
/// transparently to `a % n = b % n`, so every lemma this schema targets is a
/// plain `Eq`/`Iff` combinator once that unfolding is taken. The producer never
/// names `Int`, `Nat`, `ModEq`, `%`, or any target or sibling declaration.
///
/// The returned proof is **untrusted**; see
/// [`propose_bounded_induction`](fn.propose_bounded_induction.html).
///
/// # Errors
///
/// Raises `EpochError` if `goal` was interned by another kernel, and `Declined`
/// carrying a typed `.reason` when the bounded search does not close the goal.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.producers")
)]
#[pyfunction]
fn propose_modeq_family(
    py: Python<'_>,
    mut kernel: PyRefMut<'_, PyKernel>,
    goal: PyExprId,
) -> PyResult<PyModEqCandidate> {
    let id = kernel.expr_of(goal)?;
    let inner = kernel.inner_mut();
    let proposed = py.detach(move || modeq_family::propose_modeq_family(inner, id));
    match proposed {
        Ok(candidate) => {
            let proof = kernel.wrap_expr(candidate.proof);
            Ok(PyModEqCandidate {
                proof,
                binders_used: candidate.binders_used,
            })
        }
        Err(reason) => Err(PyDeclineReason::from_modeq(&reason).into_declined(py)),
    }
}

/// Audits an already-admitted `candidate` against its `target`.
///
/// A pure function of the kernel's own dependency graph: the same check the
/// `modeq_family_operation` driver runs, and the same one the adversarial
/// fixture in `tests/modeq_family_operation.rs` proves actually rejects a
/// candidate built to cite its own target.
///
/// # Errors
///
/// Raises `EpochError` if either name was interned by another kernel.
// `PyO3` extracts OWNED values across the FFI edge, so the handles are by value
// whether or not the body consumes them.
#[allow(clippy::needless_pass_by_value)]
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.producers")
)]
#[pyfunction]
fn audit_circularity(
    kernel: PyRef<'_, PyKernel>,
    candidate: PyNameId,
    target: PyNameId,
) -> PyResult<PyCircularityAudit> {
    let candidate = kernel.name_of(candidate)?;
    let target = kernel.name_of(target)?;
    let audit = modeq_family::audit_circularity(kernel.inner(), candidate, target);
    Ok(PyCircularityAudit {
        target_dependency: audit.target_dependency,
        axiom_footprint: audit.axiom_footprint,
        theorem_dependencies: audit.theorem_dependencies,
    })
}

/// Registers the `producers` submodule on `parent` and returns it.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    // The FULL dotted name, so `repr(axeyum.producers)` and every traceback
    // name the module the way an import statement spells it.
    let module = PyModule::new(py, "axeyum._native.producers")?;
    module.add_class::<PyDeclineReason>()?;
    module.add_class::<PyCandidate>()?;
    module.add_class::<PyApplicationCandidate>()?;
    module.add_class::<PyModEqCandidate>()?;
    module.add_class::<PyCircularityAudit>()?;
    module.add_class::<PyImportLimits>()?;
    module.add_class::<PyImportReport>()?;
    module.add_class::<PyAxiomIdentity>()?;
    module.add_class::<PyDeclarationIdentity>()?;
    module.add_class::<PyDeclarationDependency>()?;
    module.add_class::<PyStatementImport>()?;
    module.add_class::<PyCandidateTransport>()?;
    module.add(
        "StatementImportError",
        py.get_type::<StatementImportError>(),
    )?;
    module.add(
        "CandidateTransportError",
        py.get_type::<CandidateTransportError>(),
    )?;
    module.add("Declined", py.get_type::<Declined>())?;
    // Pinned budgets, exported as constants and reachable through no argument.
    // `MAX_BINDERS` is part of five settled facts' reproduction contract.
    module.add("MAX_BINDERS", bounded_induction::MAX_BINDERS)?;
    module.add("MAX_INDUCTIONS", bounded_induction::MAX_INDUCTIONS)?;
    module.add(
        "MAX_RETRIEVED_DECLARATIONS",
        bounded_induction::MAX_RETRIEVED_DECLARATIONS,
    )?;
    module.add("APPLICATION_MAX_BINDERS", bounded_application::MAX_BINDERS)?;
    module.add(
        "APPLICATION_MAX_DEPTH",
        bounded_application::MAX_APPLICATION_DEPTH,
    )?;
    module.add("APPLICATION_MAX_TERMS", bounded_application::MAX_TERMS)?;
    module.add("MODEQ_MAX_BINDERS", modeq_family::MAX_BINDERS)?;
    module.add("FORMAT_VERSION", axeyum_lean_import::FORMAT_VERSION)?;
    module.add("IDENTITY_VERSION", axeyum_lean_import::IDENTITY_VERSION)?;
    module.add_function(wrap_pyfunction!(import_statement_ndjson, &module)?)?;
    module.add_function(wrap_pyfunction!(
        import_candidate_statement_ndjson,
        &module
    )?)?;
    module.add_function(wrap_pyfunction!(transport_native_candidate, &module)?)?;
    module.add_function(wrap_pyfunction!(propose_bounded_induction, &module)?)?;
    module.add_function(wrap_pyfunction!(
        propose_bounded_induction_with_rewrites,
        &module
    )?)?;
    module.add_function(wrap_pyfunction!(propose_bounded_application, &module)?)?;
    module.add_function(wrap_pyfunction!(propose_modeq_family, &module)?)?;
    module.add_function(wrap_pyfunction!(audit_circularity, &module)?)?;
    parent.add("producers", &module)?;
    Ok(module)
}

#[cfg(test)]
mod tests {
    use super::{DEFAULT_MAX_LINE_BYTES, DEFAULT_MAX_RECORDS, ImportLimits, PyImportLimits};

    /// The defaults in `PyImportLimits::new`'s signature must be the Rust ones.
    ///
    /// It reads the same two `const`s the signature does, so a drift on EITHER
    /// side kills it. Mutation-checked both ways: changing either `const`, or
    /// changing `ImportLimits::default()`, fails this test and nothing else in
    /// the Rust suite. (Written first with the literals repeated here, where it
    /// survived a mutation of the signature and pinned nothing.)
    #[test]
    fn binding_defaults_match_rust() {
        let quoted = PyImportLimits::new(DEFAULT_MAX_LINE_BYTES, DEFAULT_MAX_RECORDS);
        assert_eq!(quoted.inner, ImportLimits::default());
    }
}

// See `crate::error`: an exception is a `PyErr` type, not a `#[pyclass]`, so the
// stub record has to be submitted separately -- and both exceptions here carry a
// payload attached with `setattr` at the RAISE site, which exists in no
// signature. `Declined.reason` in particular is read by
// `python/axeyum/agent/tools.py`, where it was an unresolved attribute under
// `ty` until it was declared here.
#[cfg(feature = "stub-gen")]
mod stub {
    use super::{CandidateTransportError, Declined, PyDeclineReason, StatementImportError};
    use crate::error::AxeyumError;
    use crate::stub_info::stub_exception;

    stub_exception!(
        "axeyum._native.producers",
        Declined,
        AxeyumError,
        "A producer declined the goal. `unknown` and `declined` are values, and this is how the value crosses a `raise`.",
        "reason": PyDeclineReason = "The typed refusal: which producer, which kind, and its detail.",
    );
    stub_exception!(
        "axeyum._native.producers",
        StatementImportError,
        AxeyumError,
        "A `lean4export` statement could not be imported.",
        "variant": String = "The Rust error variant name. Never match on the message text.",
        "debug": String = "The full Rust `Debug` rendering of the failure.",
    );
    stub_exception!(
        "axeyum._native.producers",
        CandidateTransportError,
        AxeyumError,
        "A retrieved native theorem could not be checked into the imported goal kernel.",
        "variant": String = "The Rust composition error variant name. Never match on the message text.",
        "debug": String = "The full Rust `Debug` rendering of the failure.",
    );
}

// Module-level constants reach Python through `module.add("NAME", value)`, a
// RUNTIME call with no item for a `#[gen_stub_*]` macro to sit on -- so without
// these submissions they exist in the extension and in no stub, and a checked
// consumer reading one gets an unresolved attribute. The type is named; the
// VALUE deliberately is not, so a constant cannot drift from its stub.
#[cfg(feature = "stub-gen")]
mod stub_variables {
    pyo3_stub_gen::module_variable!("axeyum._native.producers", "APPLICATION_MAX_BINDERS", usize);
    pyo3_stub_gen::module_variable!("axeyum._native.producers", "APPLICATION_MAX_DEPTH", usize);
    pyo3_stub_gen::module_variable!("axeyum._native.producers", "APPLICATION_MAX_TERMS", usize);
    pyo3_stub_gen::module_variable!("axeyum._native.producers", "MAX_BINDERS", usize);
    pyo3_stub_gen::module_variable!("axeyum._native.producers", "MAX_INDUCTIONS", usize);
    pyo3_stub_gen::module_variable!(
        "axeyum._native.producers",
        "MAX_RETRIEVED_DECLARATIONS",
        usize
    );
    pyo3_stub_gen::module_variable!("axeyum._native.producers", "MODEQ_MAX_BINDERS", usize);
    pyo3_stub_gen::module_variable!("axeyum._native.producers", "FORMAT_VERSION", String);
    pyo3_stub_gen::module_variable!("axeyum._native.producers", "IDENTITY_VERSION", String);
}
