//! Fail-closed import of official `lean4export` NDJSON into the independent
//! Axeyum Lean kernel.
//!
//! This crate is deliberately separate from `axeyum-lean-kernel`: JSON parsing,
//! format-version dispatch, resource limits, and malformed-input diagnostics are
//! untrusted boundary code. Only [`Kernel::add_declaration`],
//! [`Kernel::add_inductive`], and [`Kernel::add_mutual_inductive`] decide
//! whether translated declarations enter the independently checked
//! environment.
//!
//! The initial profile is official `lean4export` format 3.1.0. It translates
//! names, universe levels, the expression forms already represented by the
//! kernel, safe non-inductive declarations, and ordered one- or multi-family
//! inductive groups. It translates projections and natural literals, compares
//! kernel-derived nested-inductive auxiliary recursors by checked name, and
//! rejects unsupported string literals, unsafe or partial declarations,
//! unknown records, and malformed/forward references. Quotient records are
//! buffered as one exact ordered package and sent through the kernel's atomic
//! canonical-package gate. Reflexive
//! and nested-count metadata are descriptive; the independent kernel decides
//! support from the translated terms. [`import_ndjson`] owns a private staging
//! kernel and publishes it only after the complete stream succeeds, so an error
//! cannot expose a partial environment.
//!
//! Each completed [`ImportReport`] also carries ADR-0350's versioned canonical
//! identity manifest: TL0.4-compatible axiom name/type hashes plus complete
//! structural content and direct-dependency digests for every independently
//! admitted declaration. These identities ignore wire and arena allocation
//! order; they do not authenticate the producer-intended stream length.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io::{self, BufRead, Read};

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, InductiveFamilySpec, Kernel, KernelError, LevelId, Lit,
    NameId, NatLit, QuotKind, RecRule, ReducibilityHint,
};
use serde_json::{Map, Value};

mod candidate_transport;
mod checked_theorem_receipt;
mod contract_residualization;
mod identity;
mod nat_le_brecon_substitution;
mod nat_no_confusion_substitution;
mod nat_order_substitution;
pub mod producers;
mod semantic_contract_receipt;
mod source_delta_trace;
mod statement_goal_record;
pub mod tactic_bridge;
mod theorem_composition;
mod theorem_specialization;
pub mod thin_adapter;
mod trace_contract_receipt;
mod trace_contract_theorem_receipt;
mod trusted_substitution;
mod type_slice;
mod type_slice_receipt;

pub use candidate_transport::{
    CandidateTransportReceipt, CompletedCandidateTransport, transport_checked_theorem_candidate,
};
pub use checked_theorem_receipt::{
    CHECKED_DEPENDENCY_THEOREM_RECEIPT_VERSION, CHECKED_SEMANTIC_THEOREM_RECEIPT_VERSION,
    CheckedDependencyTheoremAuthority, CheckedDependencyTheoremReceipt,
    CheckedDependencyTheoremReceiptError, CheckedSemanticTheoremReceipt,
    CheckedSemanticTheoremReceiptError, CheckedTheoremAuthority, CheckedTheoremDependency,
    issue_checked_dependency_theorem_receipt, issue_checked_semantic_theorem_receipt,
    verify_checked_dependency_theorem_receipt, verify_checked_semantic_theorem_receipt,
};
pub use contract_residualization::{
    ResidualizedFunctionContract, ResidualizedFunctionContractError,
    residualize_function_contract_body,
};
pub use identity::{
    AxiomIdentity, DeclarationDependencyIdentity, DeclarationIdentity, DeclarationKind,
    canonical_alpha_expression_sha256, canonical_declaration_sha256, canonical_expression_sha256,
    canonical_kernel_type_shape_sha256, canonical_level_sha256,
};
pub use semantic_contract_receipt::{
    SEMANTIC_FUNCTION_CONTRACT_RECEIPT_VERSION, SemanticContractDependencyReceipt,
    SemanticFunctionContractReceipt, SemanticFunctionContractReceiptError,
    issue_semantic_function_contract_receipt, verify_semantic_function_contract_receipt,
};
pub use source_delta_trace::{
    CheckedSourceDeltaStep, SourceDeltaStepError, build_source_delta_step, verify_source_delta_step,
};
pub use statement_goal_record::{
    StatementGoalRecord, StatementGoalRecordError, build_statement_goal_record,
};
pub use theorem_composition::{
    AddedDefinitionReceipt, AddedSingletonInductiveReceipt, AddedTheoremReceipt,
    CHECKED_TARGET_LEAF_THEOREM_COMPOSITION_VERSION, CHECKED_THEOREM_COMPOSITION_VERSION,
    CheckedTheoremCompositionError, CheckedTheoremCompositionReceipt, CompletedTheoremComposition,
    PropositionCompatibilityReceipt, ReusedDeclarationReceipt, ReusedTypeCompatibility,
    checked_proposition_compatibility, checked_reused_declaration_compatibility,
    compose_checked_theorem_slice, compose_checked_theorem_slice_with_target_leaves,
    verify_checked_theorem_composition, verify_checked_theorem_composition_with_target_leaves,
};
pub use theorem_specialization::{
    CHECKED_THEOREM_SPECIALIZATION_VERSION, CheckedTheoremSpecializationError,
    CheckedTheoremSpecializationReceipt, CompletedTheoremSpecialization,
    SpecializationArgumentReceipt, specialize_checked_theorem,
    verify_checked_theorem_specialization,
};
pub use trace_contract_receipt::{
    TRACE_BACKED_SOURCE_CONTRACT_RECEIPT_VERSION, TraceBackedSourceContractReceipt,
    TraceBackedSourceContractReceiptError, TraceContractInstanceReceipt,
    issue_trace_backed_source_contract_receipt, verify_trace_backed_source_contract_receipt,
};
pub use trace_contract_theorem_receipt::{
    TRACE_BACKED_SEMANTIC_THEOREM_RECEIPT_VERSION, TraceBackedSemanticTheoremReceipt,
    TraceBackedSemanticTheoremReceiptError, issue_trace_backed_semantic_theorem_receipt,
    verify_trace_backed_semantic_theorem_receipt,
};
pub use type_slice::{
    ConstantInstance, GeneralizedBinder, GeneralizedGoal, TypeSliceError,
    generalize_goal_constants, select_definition_abstractions_auto_param_binders_v3,
    select_definition_abstractions_auto_param_v2, select_definition_abstractions_v1,
    verify_generalized_specialization,
};
pub use type_slice_receipt::{
    NORMALIZED_TYPE_SLICE_RECEIPT_VERSION, TYPE_SLICE_RECEIPT_VERSION, TypeSliceAbstractionReceipt,
    TypeSliceNormalizedDeclarationReceipt, TypeSliceReceipt, TypeSliceReceiptError,
    TypeSliceRetainedReceipt, TypeSliceSourceReceipt, TypeSliceTransportNormalizationReceipt,
    issue_type_slice_receipt, issue_type_slice_receipt_with_auto_param_normalization,
};

use identity::build_identity_manifest;

/// The only `lean4export` wire-format version admitted by this profile.
pub const FORMAT_VERSION: &str = "3.1.0";

/// Canonical identity schema used by [`ImportReport::axiom_identities`] and
/// [`ImportReport::declaration_identities`].
pub const IDENTITY_VERSION: &str = "axeyum-lean-declaration-identity-v1";

/// Resource limits applied before a stream can grow the kernel arenas without
/// bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImportLimits {
    /// Maximum bytes in one NDJSON record, including its trailing newline.
    pub max_line_bytes: usize,
    /// Maximum number of records, including the metadata record.
    pub max_records: usize,
}

impl Default for ImportLimits {
    fn default() -> Self {
        Self {
            max_line_bytes: 16 * 1024 * 1024,
            max_records: 2_000_000,
        }
    }
}

/// Counts and provenance for a successfully admitted stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportReport {
    /// Export-format version from the first record.
    pub format_version: String,
    /// Official Lean version recorded by the exporter.
    pub lean_version: String,
    /// Official Lean source hash recorded by the exporter.
    pub lean_githash: String,
    /// Exporter version recorded by the stream.
    pub exporter_version: String,
    /// Number of non-anonymous exported names.
    pub names: usize,
    /// Number of nonzero exported universe-level records.
    pub levels: usize,
    /// Number of exported expression records.
    pub expressions: usize,
    /// Number of exported declaration records. An inductive group is one record.
    pub declaration_records: usize,
    /// Number of kernel declarations admitted. An inductive group contributes
    /// its family, constructors, and generated recursor.
    pub admitted_declarations: usize,
    /// Imported axiom names. Their types were checked, but their propositions
    /// remain assumptions until discharged separately.
    pub axioms: Vec<String>,
    /// Identity schema for the axiom and declaration manifests below.
    pub identity_version: &'static str,
    /// Imported axiom names and TL0.4-compatible name/type SHA-256 identities.
    pub axiom_identities: Vec<AxiomIdentity>,
    /// Canonically ordered structural content and direct-dependency identities
    /// for every declaration admitted into the completed kernel.
    pub declaration_identities: Vec<DeclarationIdentity>,
    /// Exact rendered names of theorems this crate reconstructed and
    /// independently kernel-checked itself, in place of the untrusted
    /// wire-supplied `type`/`value` for that exact record — never populated
    /// unless [`import_statement_ndjson`]'s fixed, reviewed substitution
    /// (`trusted_substitution::SUBSTITUTABLE_THEOREMS`) fired for that name.
    /// Every name here still reports [`DeclarationKind::Theorem`] in
    /// `declaration_identities`, structurally true, so this is the field a
    /// caller must consult to tell "our own derivation" apart from "an
    /// admitted trusted declaration".
    pub substituted_theorems: Vec<String>,
}

/// One completely translated and independently admitted import.
///
/// This is the only successful publication boundary. Its fields are private so
/// callers cannot construct a completed state from an unchecked kernel or a
/// mismatched report. On import failure no `Kernel` or arena-relative handle is
/// returned. Completion is relative to the delivered bytes: format 3.1 has no
/// footer, so authenticating those bytes as the producer's intended entire
/// export requires an external digest or record manifest.
///
/// ```compile_fail
/// use axeyum_lean_import::{CompletedImport, ImportReport};
/// use axeyum_lean_kernel::Kernel;
///
/// let report = ImportReport {
///     format_version: "3.1.0".into(),
///     lean_version: "4.30.0".into(),
///     lean_githash: "untrusted".into(),
///     exporter_version: "3.1.0".into(),
///     names: 0,
///     levels: 0,
///     expressions: 0,
///     declaration_records: 0,
///     admitted_declarations: 0,
///     axioms: vec![],
///     identity_version: axeyum_lean_import::IDENTITY_VERSION,
///     axiom_identities: vec![],
///     declaration_identities: vec![],
///     substituted_theorems: vec![],
/// };
/// let forged = CompletedImport { kernel: Kernel::new(), report };
/// ```
#[derive(Debug)]
pub struct CompletedImport {
    kernel: Kernel,
    report: ImportReport,
}

/// One proof-isolated proposition imported as the value of a transparent
/// `definition : Prop`.
///
/// Unlike importing an axiom or theorem, this publishes the proposition as a
/// goal expression without adding a proof of that proposition to the checked
/// environment. Construction is available only through
/// [`import_statement_ndjson`], which rejects every axiom, theorem, opaque, and
/// quotient declaration in the delivered stream.
#[derive(Debug)]
pub struct CompletedStatementImport {
    kernel: Kernel,
    report: ImportReport,
    target_name: NameId,
    goal: ExprId,
}

impl CompletedStatementImport {
    /// Borrow the independently checked environment containing the goal's
    /// definition dependencies but no trusted or proof-bearing declaration.
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// The checked proposition to hand to an untrusted proof producer.
    #[must_use]
    pub fn goal(&self) -> ExprId {
        self.goal
    }

    /// The target definition name in this import's kernel arena.
    #[must_use]
    pub fn target_name(&self) -> NameId {
        self.target_name
    }

    /// The completed import inventory and canonical declaration identities.
    #[must_use]
    pub fn report(&self) -> &ImportReport {
        &self.report
    }

    /// Transfer the checked kernel, matching report, target name, and goal to a
    /// bounded producer/checker operation. All handles belong to the returned
    /// kernel and must not be mixed with another import.
    #[must_use]
    pub fn into_parts(self) -> (Kernel, ImportReport, NameId, ExprId) {
        (self.kernel, self.report, self.target_name, self.goal)
    }
}

/// A stream failed the stronger proof-isolated statement-adapter contract.
#[derive(Debug)]
pub enum StatementImportError {
    /// The ordinary fail-closed wire import failed.
    Import(ImportError),
    /// The exact target declaration was absent or repeated.
    TargetCardinality {
        /// Exact requested rendered declaration name.
        target: String,
        /// Number of matching declarations.
        observed: usize,
    },
    /// The target was not a transparent definition with no universe parameters.
    TargetNotDefinition {
        /// Exact requested rendered declaration name.
        target: String,
        /// Observed declaration kind.
        kind: DeclarationKind,
    },
    /// The target definition is universe-polymorphic; v1 goal receipts require
    /// one closed proposition identity.
    TargetUniverseParameters {
        /// Exact requested rendered declaration name.
        target: String,
        /// Number of universe parameters on the target.
        observed: usize,
    },
    /// The explicit candidate list repeated a declaration name.
    DuplicateCandidate,
    /// The target definition itself was offered as a candidate proof source.
    CandidateIsTarget {
        /// Exact requested target name.
        target: String,
    },
    /// An exact candidate declaration was absent or repeated.
    CandidateCardinality {
        /// Exact requested candidate name.
        candidate: String,
        /// Number of matching declarations.
        observed: usize,
    },
    /// A checked candidate still reaches one or more trusted assumptions.
    CandidateHasAxioms {
        /// Exact requested candidate name.
        candidate: String,
        /// Number of reached trusted declarations.
        observed: usize,
    },
    /// A proof-bearing or trusted declaration entered the statement stream.
    TrustedDeclaration {
        /// Exact rendered declaration name.
        name: String,
        /// Rejected declaration kind.
        kind: DeclarationKind,
    },
    /// The target definition's value is not independently checked to inhabit
    /// `Prop`.
    GoalNotProp {
        /// Exact requested rendered declaration name.
        target: String,
    },
}

impl fmt::Display for StatementImportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Import(error) => write!(f, "statement wire import failed: {error}"),
            Self::TargetCardinality { target, observed } => {
                write!(
                    f,
                    "statement target {target:?} occurs {observed} times; expected one"
                )
            }
            Self::TargetNotDefinition { target, kind } => {
                write!(
                    f,
                    "statement target {target:?} is {kind:?}, not a definition"
                )
            }
            Self::TargetUniverseParameters { target, observed } => write!(
                f,
                "statement target {target:?} has {observed} universe parameters; expected none"
            ),
            Self::DuplicateCandidate => {
                write!(f, "candidate declaration names must be unique")
            }
            Self::CandidateIsTarget { target } => {
                write!(f, "candidate declaration list contains target {target:?}")
            }
            Self::CandidateCardinality {
                candidate,
                observed,
            } => write!(
                f,
                "candidate declaration {candidate:?} occurs {observed} times; expected one"
            ),
            Self::CandidateHasAxioms {
                candidate,
                observed,
            } => write!(
                f,
                "candidate declaration {candidate:?} reaches {observed} trusted declaration(s)"
            ),
            Self::TrustedDeclaration { name, kind } => {
                write!(
                    f,
                    "statement stream contains trusted declaration {name:?} ({kind:?})"
                )
            }
            Self::GoalNotProp { target } => {
                write!(
                    f,
                    "statement target {target:?} does not contain a Prop-valued goal"
                )
            }
        }
    }
}

impl std::error::Error for StatementImportError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Import(error) => Some(error),
            _ => None,
        }
    }
}

impl From<ImportError> for StatementImportError {
    fn from(error: ImportError) -> Self {
        Self::Import(error)
    }
}

impl CompletedImport {
    /// Borrow the independently checked completed environment.
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Borrow the inventory and provenance recorded at publication time.
    #[must_use]
    pub fn report(&self) -> &ImportReport {
        &self.report
    }

    /// Transfer ownership of the completed kernel and its matching report.
    #[must_use]
    pub fn into_parts(self) -> (Kernel, ImportReport) {
        (self.kernel, self.report)
    }
}

/// A malformed, unsupported, resource-exhausting, or kernel-rejected import.
#[derive(Debug)]
pub enum ImportError {
    /// I/O failed while reading the NDJSON stream.
    Io(io::Error),
    /// One record exceeds the configured byte limit.
    LineLimit {
        /// One-based line number.
        line: usize,
        /// Configured maximum.
        limit: usize,
    },
    /// The stream exceeds the configured record limit.
    RecordLimit {
        /// Configured maximum.
        limit: usize,
    },
    /// JSON syntax is invalid.
    Json {
        /// One-based line number.
        line: usize,
        /// Parser diagnostic.
        message: String,
    },
    /// The JSON record violates format 3.1.0 structure or topology.
    Malformed {
        /// One-based line number.
        line: usize,
        /// Deterministic diagnostic.
        message: String,
    },
    /// A well-formed format construct is outside the current admission profile.
    Unsupported {
        /// One-based line number.
        line: usize,
        /// Stable decline code.
        code: &'static str,
    },
    /// The independent kernel rejected a translated declaration.
    Kernel {
        /// One-based line number containing the declaration record.
        line: usize,
        /// Rendered declaration name or group label.
        declaration: String,
        /// Trusted gate's rejection.
        source: KernelError,
    },
}

impl fmt::Display for ImportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(f, "lean4export I/O error: {error}"),
            Self::LineLimit { line, limit } => {
                write!(f, "line {line}: record exceeds {limit} bytes")
            }
            Self::RecordLimit { limit } => write!(f, "record count exceeds {limit}"),
            Self::Json { line, message } => write!(f, "line {line}: invalid JSON: {message}"),
            Self::Malformed { line, message } => write!(f, "line {line}: {message}"),
            Self::Unsupported { line, code } => {
                write!(f, "line {line}: unsupported lean4export construct: {code}")
            }
            Self::Kernel {
                line,
                declaration,
                source,
            } => write!(f, "line {line}: kernel rejected {declaration}: {source:?}"),
        }
    }
}

impl std::error::Error for ImportError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for ImportError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

#[derive(Debug)]
struct ImportState<'kernel> {
    kernel: &'kernel mut Kernel,
    names: Vec<NameId>,
    levels: Vec<LevelId>,
    expressions: Vec<ExprId>,
    declaration_records: usize,
    axioms: Vec<String>,
    pending_quotient: Vec<Declaration>,
    quotient_complete: bool,
    /// When set, [`ImportState::import_theorem`] attempts the fixed, reviewed
    /// substitution in [`trusted_substitution`] for an exact-name match before
    /// admitting the wire-supplied theorem. Only [`import_statement_ndjson`]
    /// enables this; ordinary [`import_ndjson`] never does, so this change
    /// cannot affect a general (non-proof-isolated) import.
    trusted_substitution: bool,
    substituted_theorems: Vec<String>,
}

#[derive(Debug)]
struct ExportedInductiveFamily {
    name: NameId,
    uparams: Vec<NameId>,
    ty: ExprId,
    num_params: usize,
    num_indices: usize,
    num_nested: usize,
    constructor_names: Vec<NameId>,
    is_recursive: bool,
}

#[derive(Debug, Clone)]
struct ExportedConstructor {
    name: NameId,
    ty: ExprId,
    num_fields: u16,
}

impl<'kernel> ImportState<'kernel> {
    fn new(kernel: &'kernel mut Kernel, trusted_substitution: bool) -> Self {
        let anonymous = kernel.anon();
        let zero = kernel.level_zero();
        Self {
            kernel,
            names: vec![anonymous],
            levels: vec![zero],
            expressions: Vec::new(),
            declaration_records: 0,
            axioms: Vec::new(),
            pending_quotient: Vec::new(),
            quotient_complete: false,
            trusted_substitution,
            substituted_theorems: Vec::new(),
        }
    }

    fn name(&self, raw: &Value, line: usize, field: &str) -> Result<NameId, ImportError> {
        let index = index(raw, line, field)?;
        self.names.get(index).copied().ok_or_else(|| {
            malformed(
                line,
                format!("{field}: forward or missing name reference {index}"),
            )
        })
    }

    fn level(&self, raw: &Value, line: usize, field: &str) -> Result<LevelId, ImportError> {
        let index = index(raw, line, field)?;
        self.levels.get(index).copied().ok_or_else(|| {
            malformed(
                line,
                format!("{field}: forward or missing level reference {index}"),
            )
        })
    }

    fn expression(&self, raw: &Value, line: usize, field: &str) -> Result<ExprId, ImportError> {
        let index = index(raw, line, field)?;
        self.expressions.get(index).copied().ok_or_else(|| {
            malformed(
                line,
                format!("{field}: forward or missing expression reference {index}"),
            )
        })
    }

    fn name_array(
        &self,
        raw: &Value,
        line: usize,
        field: &str,
    ) -> Result<Vec<NameId>, ImportError> {
        array(raw, line, field)?
            .iter()
            .map(|value| self.name(value, line, field))
            .collect()
    }

    fn level_array(
        &self,
        raw: &Value,
        line: usize,
        field: &str,
    ) -> Result<Vec<LevelId>, ImportError> {
        array(raw, line, field)?
            .iter()
            .map(|value| self.level(value, line, field))
            .collect()
    }

    fn import_record(
        &mut self,
        record: &Map<String, Value>,
        line: usize,
    ) -> Result<(), ImportError> {
        let markers = ["in", "il", "ie"]
            .into_iter()
            .filter(|key| record.contains_key(*key))
            .count();
        if markers > 1 {
            return Err(malformed(line, "record has multiple index spaces"));
        }
        if record.contains_key("in") {
            return self.import_name(record, line);
        }
        if record.contains_key("il") {
            return self.import_level(record, line);
        }
        if record.contains_key("ie") {
            return self.import_expression(record, line);
        }
        self.import_declaration(record, line)
    }

    fn import_name(&mut self, record: &Map<String, Value>, line: usize) -> Result<(), ImportError> {
        let id = index(required(record, "in", line)?, line, "in")?;
        if id != self.names.len() {
            return Err(malformed(
                line,
                format!(
                    "in: expected dense name index {}, got {id}",
                    self.names.len()
                ),
            ));
        }
        let has_str = record.contains_key("str");
        let has_num = record.contains_key("num");
        if has_str == has_num || record.len() != 2 {
            return Err(malformed(
                line,
                "name record must contain exactly in plus str or num",
            ));
        }
        let name = if has_str {
            let value = object(required(record, "str", line)?, line, "str")?;
            exact_keys(value, &["pre", "str"], line, "str")?;
            let parent = self.name(required(value, "pre", line)?, line, "str.pre")?;
            let component = string(required(value, "str", line)?, line, "str.str")?;
            self.kernel.name_str(parent, component)
        } else {
            let value = object(required(record, "num", line)?, line, "num")?;
            exact_keys(value, &["pre", "i"], line, "num")?;
            let parent = self.name(required(value, "pre", line)?, line, "num.pre")?;
            let component = u64_value(required(value, "i", line)?, line, "num.i")?;
            self.kernel.name_num(parent, component)
        };
        self.names.push(name);
        Ok(())
    }

    fn import_level(
        &mut self,
        record: &Map<String, Value>,
        line: usize,
    ) -> Result<(), ImportError> {
        let id = index(required(record, "il", line)?, line, "il")?;
        if id != self.levels.len() {
            return Err(malformed(
                line,
                format!(
                    "il: expected dense level index {}, got {id}",
                    self.levels.len()
                ),
            ));
        }
        let kinds: Vec<_> = ["succ", "max", "imax", "param"]
            .into_iter()
            .filter(|key| record.contains_key(*key))
            .collect();
        if kinds.len() != 1 || record.len() != 2 {
            return Err(malformed(
                line,
                "level record must contain exactly il plus one level kind",
            ));
        }
        let level = match kinds[0] {
            "succ" => {
                let prior = self.level(required(record, "succ", line)?, line, "succ")?;
                self.kernel.level_succ(prior)
            }
            "max" | "imax" => {
                let kind = kinds[0];
                let pair = array(required(record, kind, line)?, line, kind)?;
                if pair.len() != 2 {
                    return Err(malformed(
                        line,
                        format!("{kind}: expected two level references"),
                    ));
                }
                let left = self.level(&pair[0], line, kind)?;
                let right = self.level(&pair[1], line, kind)?;
                if kind == "max" {
                    self.kernel.level_max(left, right)
                } else {
                    self.kernel.level_imax(left, right)
                }
            }
            "param" => {
                let name = self.name(required(record, "param", line)?, line, "param")?;
                self.kernel.level_param(name)
            }
            _ => unreachable!(),
        };
        self.levels.push(level);
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn import_expression(
        &mut self,
        record: &Map<String, Value>,
        line: usize,
    ) -> Result<(), ImportError> {
        let id = index(required(record, "ie", line)?, line, "ie")?;
        if id != self.expressions.len() {
            return Err(malformed(
                line,
                format!(
                    "ie: expected dense expression index {}, got {id}",
                    self.expressions.len()
                ),
            ));
        }
        let kinds: Vec<_> = [
            "bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj", "natVal", "strVal",
            "mdata",
        ]
        .into_iter()
        .filter(|key| record.contains_key(*key))
        .collect();
        if kinds.len() != 1 || record.len() != 2 {
            return Err(malformed(
                line,
                "expression record must contain exactly ie plus one expression kind",
            ));
        }
        let kind = kinds[0];
        let expression = match kind {
            "bvar" => {
                let raw = u64_value(required(record, kind, line)?, line, kind)?;
                let index = u32::try_from(raw)
                    .map_err(|_| malformed(line, "bvar does not fit the kernel index width"))?;
                self.kernel.bvar(index)
            }
            "sort" => {
                let level = self.level(required(record, kind, line)?, line, kind)?;
                self.kernel.sort(level)
            }
            "const" => {
                let value = object(required(record, kind, line)?, line, kind)?;
                exact_keys(value, &["name", "us"], line, kind)?;
                let name = self.name(required(value, "name", line)?, line, "const.name")?;
                let levels = self.level_array(required(value, "us", line)?, line, "const.us")?;
                self.kernel.const_(name, levels)
            }
            "app" => {
                let value = object(required(record, kind, line)?, line, kind)?;
                exact_keys(value, &["fn", "arg"], line, kind)?;
                let function = self.expression(required(value, "fn", line)?, line, "app.fn")?;
                let argument = self.expression(required(value, "arg", line)?, line, "app.arg")?;
                self.kernel.app(function, argument)
            }
            "lam" | "forallE" => {
                let value = object(required(record, kind, line)?, line, kind)?;
                exact_keys(value, &["name", "type", "body", "binderInfo"], line, kind)?;
                let name = self.name(required(value, "name", line)?, line, "binder.name")?;
                let ty = self.expression(required(value, "type", line)?, line, "binder.type")?;
                let body = self.expression(required(value, "body", line)?, line, "binder.body")?;
                let info = binder_info(required(value, "binderInfo", line)?, line)?;
                if kind == "lam" {
                    self.kernel.lam(name, ty, body, info)
                } else {
                    self.kernel.pi(name, ty, body, info)
                }
            }
            "letE" => {
                let value = object(required(record, kind, line)?, line, kind)?;
                exact_keys(
                    value,
                    &["name", "type", "value", "body", "nondep"],
                    line,
                    kind,
                )?;
                let name = self.name(required(value, "name", line)?, line, "letE.name")?;
                let ty = self.expression(required(value, "type", line)?, line, "letE.type")?;
                let val = self.expression(required(value, "value", line)?, line, "letE.value")?;
                let body = self.expression(required(value, "body", line)?, line, "letE.body")?;
                boolean(required(value, "nondep", line)?, line, "letE.nondep")?;
                self.kernel.let_(name, ty, val, body)
            }
            "mdata" => {
                let value = object(required(record, kind, line)?, line, kind)?;
                exact_keys(value, &["expr", "data"], line, kind)?;
                object(required(value, "data", line)?, line, "mdata.data")?;
                self.expression(required(value, "expr", line)?, line, "mdata.expr")?
            }
            "proj" => {
                let value = object(required(record, kind, line)?, line, kind)?;
                exact_keys(value, &["typeName", "idx", "struct"], line, kind)?;
                let type_name =
                    self.name(required(value, "typeName", line)?, line, "proj.typeName")?;
                let raw_index = u64_value(required(value, "idx", line)?, line, "proj.idx")?;
                let field_index = u32::try_from(raw_index)
                    .map_err(|_| malformed(line, "proj.idx exceeds the kernel field width"))?;
                let structure =
                    self.expression(required(value, "struct", line)?, line, "proj.struct")?;
                self.kernel.proj(type_name, field_index, structure)
            }
            "natVal" => {
                let digits = string(required(record, kind, line)?, line, kind)?;
                let value = NatLit::from_decimal(digits).ok_or_else(|| {
                    malformed(
                        line,
                        "natVal: expected a non-empty decimal natural-number string",
                    )
                })?;
                self.kernel.lit(Lit::Nat(value))
            }
            "strVal" => {
                // The payload is a JSON string, so escape decoding (including
                // `\uXXXX` surrogate pairs) and the rejection of invalid Unicode
                // are `serde_json`'s, and the decoded value is a sequence of
                // Unicode scalar values — exactly what Lean's kernel decodes the
                // UTF-8 payload to. Nothing is repaired or replaced here.
                let value = string(required(record, kind, line)?, line, kind)?;
                self.kernel.lit(Lit::Str(value.to_owned()))
            }
            _ => unreachable!(),
        };
        self.expressions.push(expression);
        Ok(())
    }

    fn import_declaration(
        &mut self,
        record: &Map<String, Value>,
        line: usize,
    ) -> Result<(), ImportError> {
        let kinds: Vec<_> = ["axiom", "def", "opaque", "thm", "quot", "inductive"]
            .into_iter()
            .filter(|key| record.contains_key(*key))
            .collect();
        if kinds.len() != 1 || record.len() != 1 {
            return Err(malformed(
                line,
                "expected exactly one known declaration kind",
            ));
        }
        if !self.pending_quotient.is_empty() && kinds[0] != "quot" {
            return Err(malformed(
                line,
                "declaration record interleaves an incomplete quotient package",
            ));
        }
        self.declaration_records += 1;
        match kinds[0] {
            "axiom" => self.import_axiom(required(record, "axiom", line)?, line),
            "def" => self.import_definition(required(record, "def", line)?, line),
            "opaque" => self.import_opaque(required(record, "opaque", line)?, line),
            "thm" => self.import_theorem(required(record, "thm", line)?, line),
            "quot" => self.import_quotient(required(record, "quot", line)?, line),
            "inductive" => self.import_inductive(required(record, "inductive", line)?, line),
            _ => unreachable!(),
        }
    }

    fn import_quotient(&mut self, raw: &Value, line: usize) -> Result<(), ImportError> {
        if self.quotient_complete {
            return Err(malformed(line, "duplicate quotient package"));
        }
        let value = object(raw, line, "quot")?;
        exact_keys(
            value,
            &["name", "levelParams", "type", "kind"],
            line,
            "quot",
        )?;
        let kind_text = string(required(value, "kind", line)?, line, "quot.kind")?;
        let kind = match kind_text {
            "type" => QuotKind::Type,
            "ctor" => QuotKind::Ctor,
            "lift" => QuotKind::Lift,
            "ind" => QuotKind::Ind,
            _ => return Err(malformed(line, "quot.kind is not type, ctor, lift, or ind")),
        };
        let expected = [
            QuotKind::Type,
            QuotKind::Ctor,
            QuotKind::Lift,
            QuotKind::Ind,
        ]
        .get(self.pending_quotient.len())
        .copied()
        .ok_or_else(|| malformed(line, "quotient package exceeds four declarations"))?;
        if kind != expected {
            return Err(malformed(
                line,
                format!(
                    "quot.kind is out of order: expected {}, got {kind_text}",
                    quotient_kind_name(expected)
                ),
            ));
        }
        let declaration = Declaration::Quotient {
            name: self.name(required(value, "name", line)?, line, "quot.name")?,
            uparams: self.name_array(
                required(value, "levelParams", line)?,
                line,
                "quot.levelParams",
            )?,
            ty: self.expression(required(value, "type", line)?, line, "quot.type")?,
            kind,
        };
        self.pending_quotient.push(declaration);
        if self.pending_quotient.len() == 4 {
            self.kernel
                .add_quotient_package(&self.pending_quotient)
                .map_err(|source| ImportError::Kernel {
                    line,
                    declaration: "quotient package".to_owned(),
                    source,
                })?;
            self.pending_quotient.clear();
            self.quotient_complete = true;
        }
        Ok(())
    }

    /// Drop a partially buffered quotient package. Only the census driver calls
    /// this, after recording the gate's refusal of the completed package.
    fn reset_pending_quotient(&mut self) {
        self.pending_quotient.clear();
    }

    fn finish(&self, line: usize) -> Result<(), ImportError> {
        if self.pending_quotient.is_empty() {
            Ok(())
        } else {
            Err(malformed(
                line,
                format!(
                    "incomplete quotient package at EOF: received {} of 4 declarations",
                    self.pending_quotient.len()
                ),
            ))
        }
    }

    fn import_axiom(&mut self, raw: &Value, line: usize) -> Result<(), ImportError> {
        let value = object(raw, line, "axiom")?;
        exact_keys(
            value,
            &["name", "levelParams", "type", "isUnsafe"],
            line,
            "axiom",
        )?;
        if boolean(required(value, "isUnsafe", line)?, line, "axiom.isUnsafe")? {
            return Err(unsupported(line, "declaration-unsafe"));
        }
        let name = self.name(required(value, "name", line)?, line, "axiom.name")?;
        let declaration = Declaration::Axiom {
            name,
            uparams: self.name_array(
                required(value, "levelParams", line)?,
                line,
                "axiom.levelParams",
            )?,
            ty: self.expression(required(value, "type", line)?, line, "axiom.type")?,
        };
        self.admit(declaration, line)?;
        self.axioms.push(self.kernel.display_name(name).to_string());
        Ok(())
    }

    fn import_definition(&mut self, raw: &Value, line: usize) -> Result<(), ImportError> {
        let value = object(raw, line, "def")?;
        exact_keys(
            value,
            &[
                "name",
                "levelParams",
                "type",
                "value",
                "hints",
                "safety",
                "all",
            ],
            line,
            "def",
        )?;
        if string(required(value, "safety", line)?, line, "def.safety")? != "safe" {
            return Err(unsupported(line, "declaration-unsafe-or-partial"));
        }
        self.validate_all_names(required(value, "all", line)?, line, "def.all")?;
        let hint = reducibility_hint(required(value, "hints", line)?, line)?;
        let declaration = Declaration::Definition {
            name: self.name(required(value, "name", line)?, line, "def.name")?,
            uparams: self.name_array(
                required(value, "levelParams", line)?,
                line,
                "def.levelParams",
            )?,
            ty: self.expression(required(value, "type", line)?, line, "def.type")?,
            value: self.expression(required(value, "value", line)?, line, "def.value")?,
            hint,
        };
        self.admit(declaration, line)
    }

    fn import_opaque(&mut self, raw: &Value, line: usize) -> Result<(), ImportError> {
        let value = object(raw, line, "opaque")?;
        exact_keys(
            value,
            &["name", "levelParams", "type", "value", "isUnsafe", "all"],
            line,
            "opaque",
        )?;
        if boolean(required(value, "isUnsafe", line)?, line, "opaque.isUnsafe")? {
            return Err(unsupported(line, "declaration-unsafe"));
        }
        self.validate_all_names(required(value, "all", line)?, line, "opaque.all")?;
        let declaration = Declaration::Opaque {
            name: self.name(required(value, "name", line)?, line, "opaque.name")?,
            uparams: self.name_array(
                required(value, "levelParams", line)?,
                line,
                "opaque.levelParams",
            )?,
            ty: self.expression(required(value, "type", line)?, line, "opaque.type")?,
            value: self.expression(required(value, "value", line)?, line, "opaque.value")?,
        };
        self.admit(declaration, line)
    }

    fn import_theorem(&mut self, raw: &Value, line: usize) -> Result<(), ImportError> {
        let value = object(raw, line, "thm")?;
        exact_keys(
            value,
            &["name", "levelParams", "type", "value", "all"],
            line,
            "thm",
        )?;
        self.validate_all_names(required(value, "all", line)?, line, "thm.all")?;
        let name = self.name(required(value, "name", line)?, line, "thm.name")?;
        let uparams = self.name_array(
            required(value, "levelParams", line)?,
            line,
            "thm.levelParams",
        )?;
        // Read the wire's own type/value unconditionally, so a malformed
        // record is still rejected as malformed regardless of the name — but
        // for the fixed, reviewed substitution set, in statement-isolation
        // mode only, they are parsed and then discarded rather than admitted:
        // see `trusted_substitution` for what is admitted instead and why.
        let wire_ty = self.expression(required(value, "type", line)?, line, "thm.type")?;
        let wire_value = self.expression(required(value, "value", line)?, line, "thm.value")?;
        let declaration = if self.trusted_substitution {
            let rendered = self.kernel.display_name(name).to_string();
            match trusted_substitution::reconstruct(self.kernel, name, &rendered, wire_ty) {
                Ok(Some(substituted)) => {
                    self.substituted_theorems.push(rendered);
                    substituted
                }
                // `Ok(None)`: the name is not in the fixed substitution set,
                // nothing to do. `Err(_)`: it IS in that set but reconstruction
                // failed for this kernel — fall back to admitting the wire's
                // own theorem exactly as an ordinary import would. Neither
                // case weakens the statement-isolation contract: a name that
                // fails to reconstruct is still a Theorem-kind declaration in
                // the environment, and `import_statement_ndjson`'s
                // trusted-declaration check (which only ever exempts names
                // actually recorded in `substituted_theorems`) still refuses
                // it exactly as before.
                Ok(None) | Err(_) => Declaration::Theorem {
                    name,
                    uparams,
                    ty: wire_ty,
                    value: wire_value,
                },
            }
        } else {
            Declaration::Theorem {
                name,
                uparams,
                ty: wire_ty,
                value: wire_value,
            }
        };
        self.admit(declaration, line)
    }

    #[allow(clippy::too_many_lines)]
    fn import_inductive(&mut self, raw: &Value, line: usize) -> Result<(), ImportError> {
        let group = object(raw, line, "inductive")?;
        exact_keys(group, &["types", "ctors", "recs"], line, "inductive")?;
        let types = array(required(group, "types", line)?, line, "inductive.types")?;
        let constructors = array(required(group, "ctors", line)?, line, "inductive.ctors")?;
        let recursors = array(required(group, "recs", line)?, line, "inductive.recs")?;
        if types.is_empty() {
            return Err(malformed(line, "inductive group has no family types"));
        }

        // `numNested` is descriptive wire metadata, never admission authority.
        // Parse its group-wide shape now, then compare it only after the
        // independent kernel has generated the checked recursor population.
        let nested_counts = types
            .iter()
            .map(|raw_type| {
                let ty = object(raw_type, line, "inductive.type")?;
                usize_value(
                    required(ty, "numNested", line)?,
                    line,
                    "inductive.type.numNested",
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let nested_count = nested_counts[0];
        if nested_counts.iter().any(|&count| count != nested_count) {
            return Err(malformed(line, "mutual family numNested differs"));
        }
        let group_names = types
            .iter()
            .map(|raw_type| {
                let ty = object(raw_type, line, "inductive.type")?;
                self.name(required(ty, "name", line)?, line, "inductive.type.name")
            })
            .collect::<Result<Vec<_>, _>>()?;
        if group_names.iter().copied().collect::<BTreeSet<_>>().len() != group_names.len() {
            return Err(malformed(line, "inductive group repeats a family name"));
        }

        let mut exported_families = Vec::with_capacity(types.len());
        for (raw_type, &num_nested) in types.iter().zip(&nested_counts) {
            let ty = object(raw_type, line, "inductive.type")?;
            exact_keys(
                ty,
                &[
                    "name",
                    "levelParams",
                    "type",
                    "numParams",
                    "numIndices",
                    "all",
                    "ctors",
                    "numNested",
                    "isRec",
                    "isUnsafe",
                    "isReflexive",
                ],
                line,
                "inductive.type",
            )?;
            if boolean(
                required(ty, "isUnsafe", line)?,
                line,
                "inductive.type.isUnsafe",
            )? {
                return Err(unsupported(line, "declaration-unsafe"));
            }
            // Descriptive frontend metadata never authorizes or denies the
            // independent structural gate.
            boolean(
                required(ty, "isReflexive", line)?,
                line,
                "inductive.type.isReflexive",
            )?;
            let all = self.name_array(required(ty, "all", line)?, line, "inductive.type.all")?;
            if all != group_names {
                return Err(malformed(
                    line,
                    "inductive type all list differs from ordered group",
                ));
            }
            exported_families.push(ExportedInductiveFamily {
                name: self.name(required(ty, "name", line)?, line, "inductive.type.name")?,
                uparams: self.name_array(
                    required(ty, "levelParams", line)?,
                    line,
                    "inductive.type.levelParams",
                )?,
                ty: self.expression(required(ty, "type", line)?, line, "inductive.type.type")?,
                num_params: usize_value(
                    required(ty, "numParams", line)?,
                    line,
                    "inductive.type.numParams",
                )?,
                num_indices: usize_value(
                    required(ty, "numIndices", line)?,
                    line,
                    "inductive.type.numIndices",
                )?,
                num_nested,
                constructor_names: self.name_array(
                    required(ty, "ctors", line)?,
                    line,
                    "inductive.type.ctors",
                )?,
                is_recursive: boolean(required(ty, "isRec", line)?, line, "inductive.type.isRec")?,
            });
        }

        let common_uparams = exported_families[0].uparams.clone();
        let common_num_params = exported_families[0].num_params;
        for family in &exported_families {
            if family.uparams != common_uparams {
                return Err(malformed(line, "mutual family universe parameters differ"));
            }
            if family.num_params != common_num_params {
                return Err(malformed(line, "mutual family numParams differs"));
            }
        }

        let ordered_constructor_names = exported_families
            .iter()
            .flat_map(|family| family.constructor_names.iter().copied())
            .collect::<Vec<_>>();
        if ordered_constructor_names.len() != constructors.len() {
            return Err(malformed(
                line,
                "constructor-name lists do not match ctor record count",
            ));
        }

        let mut parsed_constructors = BTreeMap::new();
        let mut wire_constructor_names = Vec::with_capacity(constructors.len());
        for raw_ctor in constructors {
            let ctor = object(raw_ctor, line, "inductive.ctor")?;
            exact_keys(
                ctor,
                &[
                    "name",
                    "levelParams",
                    "type",
                    "induct",
                    "cidx",
                    "numParams",
                    "numFields",
                    "isUnsafe",
                ],
                line,
                "inductive.ctor",
            )?;
            if boolean(
                required(ctor, "isUnsafe", line)?,
                line,
                "inductive.ctor.isUnsafe",
            )? {
                return Err(unsupported(line, "declaration-unsafe"));
            }
            let ctor_name =
                self.name(required(ctor, "name", line)?, line, "inductive.ctor.name")?;
            let parent = self.name(
                required(ctor, "induct", line)?,
                line,
                "inductive.ctor.induct",
            )?;
            let Some(owner_index) = group_names.iter().position(|&name| name == parent) else {
                return Err(malformed(
                    line,
                    "constructor parent is not in the ordered group",
                ));
            };
            let cidx = usize_value(required(ctor, "cidx", line)?, line, "inductive.ctor.cidx")?;
            if exported_families[owner_index].constructor_names.get(cidx) != Some(&ctor_name) {
                return Err(malformed(
                    line,
                    "constructor parent/index/name differs from family list",
                ));
            }
            let constructor_parameter_count = usize_value(
                required(ctor, "numParams", line)?,
                line,
                "inductive.ctor.numParams",
            )?;
            if constructor_parameter_count != common_num_params {
                return Err(malformed(line, "constructor numParams differs from family"));
            }
            let ctor_uparams = self.name_array(
                required(ctor, "levelParams", line)?,
                line,
                "inductive.ctor.levelParams",
            )?;
            if ctor_uparams != common_uparams {
                return Err(malformed(
                    line,
                    "constructor universe parameters differ from family",
                ));
            }
            let field_count = u64_value(
                required(ctor, "numFields", line)?,
                line,
                "inductive.ctor.numFields",
            )?;
            let field_count = u16::try_from(field_count)
                .map_err(|_| malformed(line, "constructor field count exceeds kernel width"))?;
            let ctor_type =
                self.expression(required(ctor, "type", line)?, line, "inductive.ctor.type")?;
            wire_constructor_names.push(ctor_name);
            if parsed_constructors
                .insert(
                    ctor_name,
                    ExportedConstructor {
                        name: ctor_name,
                        ty: ctor_type,
                        num_fields: field_count,
                    },
                )
                .is_some()
            {
                return Err(malformed(
                    line,
                    "inductive group repeats a constructor record",
                ));
            }
        }
        if wire_constructor_names != ordered_constructor_names {
            return Err(malformed(
                line,
                "constructor records differ from family/constructor order",
            ));
        }

        let family_specs = exported_families
            .iter()
            .map(|family| {
                let constructors = family
                    .constructor_names
                    .iter()
                    .map(|name| {
                        parsed_constructors
                            .get(name)
                            .map(|constructor| (constructor.name, constructor.ty))
                            .ok_or_else(|| malformed(line, "family constructor record is missing"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(InductiveFamilySpec::new(
                    family.name,
                    family.ty,
                    constructors,
                ))
            })
            .collect::<Result<Vec<_>, ImportError>>()?;

        let group_label = self
            .kernel
            .display_name(exported_families[0].name)
            .to_string();
        self.kernel
            .add_mutual_inductive(&common_uparams, common_num_params, &family_specs)
            .map_err(|source| ImportError::Kernel {
                line,
                declaration: group_label,
                source,
            })?;

        self.validate_generated_families(&exported_families, line)?;
        for (family, spec) in exported_families.iter().zip(&family_specs) {
            let fields = family
                .constructor_names
                .iter()
                .map(|name| parsed_constructors[name].num_fields)
                .collect::<Vec<_>>();
            self.validate_generated_constructors(
                family.name,
                &common_uparams,
                &spec.constructors,
                &fields,
                line,
            )?;
        }

        let mut main_recursor_names = Vec::with_capacity(exported_families.len());
        for family in &exported_families {
            main_recursor_names.push(self.kernel.name_str(family.name, "rec"));
        }
        let first_main = self
            .kernel
            .environment()
            .get(main_recursor_names[0])
            .cloned()
            .ok_or_else(|| malformed(line, "kernel did not generate source main recursor"))?;
        let Declaration::Recursor { num_motives, .. } = first_main else {
            return Err(malformed(
                line,
                "generated source main name is not a recursor",
            ));
        };
        let derived_nested_count = usize::from(num_motives)
            .checked_sub(exported_families.len())
            .ok_or_else(|| {
                malformed(
                    line,
                    "generated recursor motive count is smaller than source group",
                )
            })?;
        if exported_families
            .iter()
            .any(|family| family.num_nested != derived_nested_count)
        {
            return Err(malformed(line, "generated/exported numNested differs"));
        }
        let expected_recursor_count = exported_families
            .len()
            .checked_add(derived_nested_count)
            .ok_or_else(|| malformed(line, "inductive recursor count exceeds host width"))?;
        if derived_nested_count != 0 && recursors.len() != expected_recursor_count {
            return Err(malformed(
                line,
                "nested inductive recursor count differs from numNested",
            ));
        }
        if derived_nested_count == 0 && exported_families.len() == 1 && recursors.len() != 1 {
            return Err(malformed(
                line,
                "single-family inductive must export one recursor",
            ));
        }
        if derived_nested_count == 0 && recursors.len() != exported_families.len() {
            return Err(malformed(
                line,
                "inductive group must export one recursor per family",
            ));
        }

        let mut expected_recursors = BTreeMap::new();
        for (family_index, &name) in main_recursor_names.iter().enumerate() {
            if expected_recursors
                .insert(name, Some(family_index))
                .is_some()
            {
                return Err(malformed(line, "kernel-derived recursor names repeat"));
            }
        }
        for suffix in 1..=derived_nested_count {
            let name = self
                .kernel
                .name_str(exported_families[0].name, format!("rec_{suffix}"));
            if expected_recursors.insert(name, None).is_some() {
                return Err(malformed(line, "kernel-derived recursor names repeat"));
            }
        }
        let mut recursor_records = BTreeMap::new();
        for raw_recursor in recursors {
            let rec = object(raw_recursor, line, "inductive.rec")?;
            let name = self.name(required(rec, "name", line)?, line, "inductive.rec.name")?;
            if !expected_recursors.contains_key(&name) {
                return Err(malformed(
                    line,
                    "exported recursor name does not belong to kernel-derived group",
                ));
            }
            if recursor_records.insert(name, raw_recursor).is_some() {
                return Err(malformed(line, "inductive group repeats a recursor record"));
            }
        }
        for (recursor_name, family_index) in expected_recursors {
            let raw_recursor = recursor_records
                .get(&recursor_name)
                .ok_or_else(|| malformed(line, "kernel-derived recursor record is missing"))?;
            self.validate_generated_recursor(
                raw_recursor,
                recursor_name,
                family_index.map(|index| exported_families[index].num_indices),
                &group_names,
                derived_nested_count != 0,
                line,
            )?;
        }
        Ok(())
    }

    fn validate_generated_families(
        &mut self,
        exported: &[ExportedInductiveFamily],
        line: usize,
    ) -> Result<(), ImportError> {
        for family in exported {
            let generated = self
                .kernel
                .environment()
                .get(family.name)
                .cloned()
                .ok_or_else(|| malformed(line, "kernel did not generate exported family"))?;
            let Declaration::Inductive {
                uparams,
                ty,
                num_params,
                num_indices,
                is_recursive,
                ctor_names,
                ..
            } = generated
            else {
                return Err(malformed(
                    line,
                    "generated family name has wrong declaration kind",
                ));
            };
            if uparams != family.uparams
                || !self.kernel.def_eq(ty, family.ty)
                || usize::from(num_params) != family.num_params
                || usize::from(num_indices) != family.num_indices
                || is_recursive != family.is_recursive
                || ctor_names != family.constructor_names
            {
                return Err(malformed(
                    line,
                    "generated/exported family metadata or type differs",
                ));
            }
        }
        Ok(())
    }

    fn validate_generated_constructors(
        &mut self,
        inductive: NameId,
        uparams: &[NameId],
        constructors: &[(NameId, ExprId)],
        field_counts: &[u16],
        line: usize,
    ) -> Result<(), ImportError> {
        for (expected_index, ((name, exported_type), exported_fields)) in constructors
            .iter()
            .copied()
            .zip(field_counts.iter().copied())
            .enumerate()
        {
            let generated = self
                .kernel
                .environment()
                .get(name)
                .cloned()
                .ok_or_else(|| malformed(line, "kernel did not generate exported constructor"))?;
            let Declaration::Constructor {
                uparams: generated_uparams,
                ty,
                inductive: generated_parent,
                idx,
                num_fields,
                ..
            } = generated
            else {
                return Err(malformed(
                    line,
                    "generated constructor name has wrong declaration kind",
                ));
            };
            if generated_uparams != uparams
                || generated_parent != inductive
                || usize::from(idx) != expected_index
                || num_fields != exported_fields
                || !self.kernel.def_eq(ty, exported_type)
            {
                return Err(malformed(
                    line,
                    "generated/exported constructor metadata or type differs",
                ));
            }
        }
        Ok(())
    }

    fn validate_generated_recursor(
        &mut self,
        raw: &Value,
        expected_name: NameId,
        exported_num_indices: Option<usize>,
        expected_all: &[NameId],
        is_nested: bool,
        line: usize,
    ) -> Result<(), ImportError> {
        let rec = object(raw, line, "inductive.rec")?;
        exact_keys(
            rec,
            &[
                "name",
                "levelParams",
                "type",
                "all",
                "numParams",
                "numIndices",
                "numMotives",
                "numMinors",
                "rules",
                "k",
                "isUnsafe",
            ],
            line,
            "inductive.rec",
        )?;
        self.validate_recursor_group_metadata(rec, expected_all, is_nested, line)?;
        let name = self.name(required(rec, "name", line)?, line, "inductive.rec.name")?;
        if name != expected_name {
            return Err(malformed(
                line,
                "exported recursor name differs from kernel-derived name",
            ));
        }
        let exported_type =
            self.expression(required(rec, "type", line)?, line, "inductive.rec.type")?;
        let exported_uparams = self.name_array(
            required(rec, "levelParams", line)?,
            line,
            "inductive.rec.levelParams",
        )?;
        let generated = self
            .kernel
            .environment()
            .get(name)
            .cloned()
            .ok_or_else(|| malformed(line, "kernel did not generate exported recursor"))?;
        let Declaration::Recursor {
            uparams,
            ty,
            rec_rules,
            num_motives,
            num_minors,
            num_params,
            num_indices,
            ..
        } = generated
        else {
            return Err(malformed(line, "generated name is not a recursor"));
        };
        // Universe closure on the WIRE's own terms, BEFORE the alpha-rename.
        //
        // `recursor_universe_substitution` maps the exported `levelParams`
        // positionally onto the ones this kernel generated. A parameter the
        // exported type mentions but the exported list does NOT bind is not in
        // that map, so the substitution leaves it exactly as it is — and if it
        // happens to spell the same name the generated recursor uses, `def_eq`
        // succeeds and the record is accepted with a binding list that binds
        // something else entirely. `def_eq` cannot see this: it treats an
        // unbound `Param` exactly like a bound one, which is the same reason
        // `Kernel::check_declaration` had to make universe closure its own
        // check rather than lean on inference.
        //
        // Found by the kernel-vs-kernel wire differential on 2026-08-18
        // (`ind.rec-uparams`): renaming `True.rec`'s or `Acc.rec`'s motive
        // universe parameter at the binding site was admitted here and
        // contradicted by the recursor Lean's own kernel generated for the same
        // family (`Sort u` against `Sort uparam.0`). The recursor record is the
        // one place this had to be checked here rather than in the kernel: a
        // recursor is *generated* and then compared, never admitted from the
        // stream, so the kernel is never handed the exported binding list.
        // Order matters, and the reason is a masking incident this change caused
        // and then had to undo: `recursor_universe_substitution` rejects an
        // exported list of the WRONG LENGTH, and
        // `official_nested_inductive_groups::recursor_metadata_mutations_reject_exactly`
        // pins that message for a truncated list. Running the closure check
        // first made a truncated list report "unbound universe parameter"
        // instead — a new guard silently taking over an old guard's cases,
        // which is how a guard stops guarding without anything going red.
        let universe_substitution =
            self.recursor_universe_substitution(&exported_uparams, &uparams, line)?;
        self.require_universe_closed(exported_type, &exported_uparams, "type", line)?;
        let renamed_exported_type = self
            .kernel
            .substitute_expr_levels(exported_type, &universe_substitution);
        if !self.kernel.def_eq(ty, renamed_exported_type) {
            return Err(malformed(
                line,
                "generated/exported recursor types are not definitionally equal",
            ));
        }
        let fields = [
            ("numParams", usize::from(num_params)),
            ("numIndices", usize::from(num_indices)),
            ("numMotives", usize::from(num_motives)),
            ("numMinors", usize::from(num_minors)),
        ];
        for (field, generated_value) in fields {
            let exported = usize_value(required(rec, field, line)?, line, field)?;
            if exported != generated_value {
                return Err(malformed(
                    line,
                    format!("generated/exported recursor {field} differs"),
                ));
            }
        }
        if let Some(exported_num_indices) = exported_num_indices
            && usize::from(num_indices) != exported_num_indices
        {
            return Err(malformed(
                line,
                "generated family index count differs from export",
            ));
        }
        self.validate_rec_rules(
            required(rec, "rules", line)?,
            &rec_rules,
            &exported_uparams,
            &universe_substitution,
            line,
        )
    }

    fn validate_recursor_group_metadata(
        &self,
        rec: &Map<String, Value>,
        expected_all: &[NameId],
        is_nested: bool,
        line: usize,
    ) -> Result<(), ImportError> {
        if boolean(
            required(rec, "isUnsafe", line)?,
            line,
            "inductive.rec.isUnsafe",
        )? {
            return Err(unsupported(line, "declaration-unsafe"));
        }
        let is_k_target = boolean(required(rec, "k", line)?, line, "inductive.rec.k")?;
        if is_nested && is_k_target {
            return Err(malformed(line, "nested recursor may not be a K target"));
        }
        if expected_all.len() > 1 && is_k_target {
            return Err(malformed(line, "mutual recursor may not be a K target"));
        }
        // `k` is not descriptive metadata. It licenses ι-reduction of a
        // recursor application whose major premise is not a constructor, so a
        // wrong flag on the wire is a wrong reduction rule for every consumer
        // that trusts it. Every other recursor field is compared against the
        // one this kernel generated; `k` was the one that was not, and the
        // kernel-vs-kernel differential found it on 2026-08-18 — flipping it
        // was admitted here and contradicted by the recursor Lean's kernel
        // generated for the same family.
        //
        // The two cases above already pin `k = false` for nested and mutual
        // recursors, which is the whole reason they are checked first; what
        // remains is the single-family case, where the kernel's own predicate
        // is the answer.
        if !is_nested
            && expected_all.len() == 1
            && is_k_target != self.kernel.is_k_like_inductive(expected_all[0])
        {
            return Err(malformed(
                line,
                "exported recursor K-like flag differs from the kernel-derived one",
            ));
        }
        let all = self.name_array(required(rec, "all", line)?, line, "inductive.rec.all")?;
        if all != expected_all {
            return Err(malformed(
                line,
                "inductive recursor all list differs from ordered group",
            ));
        }
        Ok(())
    }

    fn recursor_universe_substitution(
        &mut self,
        exported: &[NameId],
        generated: &[NameId],
        line: usize,
    ) -> Result<Vec<(NameId, LevelId)>, ImportError> {
        if generated.len() != exported.len() {
            return Err(malformed(
                line,
                "generated/exported recursor universe-parameter arity differs",
            ));
        }
        // Universe parameter names are binders, so the official exporter and
        // Axeyum may choose different fresh names (for example `u_1` versus
        // `u.1`) without a semantic difference. Alpha-rename the exported
        // recursor into the generated parameter namespace before comparison.
        Ok(exported
            .iter()
            .copied()
            .zip(generated.iter().copied())
            .map(|(exported, generated)| (exported, self.kernel.level_param(generated)))
            .collect())
    }

    /// Reject an exported recursor term that mentions a universe parameter the
    /// recursor's own `levelParams` does not bind.
    ///
    /// Two call sites, and they are separate guards on purpose: the type and an
    /// ι-rule right-hand side are separate expressions, and a stream can leave
    /// one closed while the other is not. Each is driven to failure
    /// individually in `tests/recursor_universe_params_must_be_bound.rs`.
    fn require_universe_closed(
        &mut self,
        expression: ExprId,
        uparams: &[NameId],
        what: &str,
        line: usize,
    ) -> Result<(), ImportError> {
        let Some(stray) = self.kernel.undeclared_universe_param(expression, uparams) else {
            return Ok(());
        };
        let stray = self.kernel.display_name(stray).to_string();
        Err(malformed(
            line,
            format!("exported recursor {what} mentions unbound universe parameter {stray}"),
        ))
    }

    fn validate_rec_rules(
        &mut self,
        raw: &Value,
        generated: &[RecRule],
        exported_uparams: &[NameId],
        universe_substitution: &[(NameId, LevelId)],
        line: usize,
    ) -> Result<(), ImportError> {
        let exported = array(raw, line, "inductive.rec.rules")?;
        if exported.len() != generated.len() {
            return Err(malformed(
                line,
                "generated/exported recursor rule count differs",
            ));
        }
        for (raw_rule, generated_rule) in exported.iter().zip(generated) {
            let rule = object(raw_rule, line, "inductive.rec.rule")?;
            exact_keys(
                rule,
                &["ctor", "nfields", "rhs"],
                line,
                "inductive.rec.rule",
            )?;
            let ctor = self.name(
                required(rule, "ctor", line)?,
                line,
                "inductive.rec.rule.ctor",
            )?;
            let fields = u64_value(
                required(rule, "nfields", line)?,
                line,
                "inductive.rec.rule.nfields",
            )?;
            let fields = u16::try_from(fields)
                .map_err(|_| malformed(line, "recursor field count exceeds kernel width"))?;
            let rhs =
                self.expression(required(rule, "rhs", line)?, line, "inductive.rec.rule.rhs")?;
            // Same closure check as the recursor type, for the same reason: an
            // ι-rule right-hand side is an exported term compared under the
            // positional alpha-rename, so a parameter outside the exported
            // binding list passes through the map untouched.
            self.require_universe_closed(rhs, exported_uparams, "rule", line)?;
            let renamed_rhs = self
                .kernel
                .substitute_expr_levels(rhs, universe_substitution);
            if generated_rule.ctor_name != ctor
                || generated_rule.num_fields != fields
                || !self.kernel.def_eq(generated_rule.value, renamed_rhs)
            {
                return Err(malformed(line, "generated/exported recursor rule differs"));
            }
        }
        Ok(())
    }

    fn validate_all_names(&self, raw: &Value, line: usize, field: &str) -> Result<(), ImportError> {
        self.name_array(raw, line, field).map(|_| ())
    }

    fn admit(&mut self, declaration: Declaration, line: usize) -> Result<(), ImportError> {
        let name = self.kernel.display_name(declaration.name()).to_string();
        self.kernel
            .add_declaration(declaration)
            .map_err(|source| ImportError::Kernel {
                line,
                declaration: name,
                source,
            })
    }
}

/// Read, translate, and independently admit one `lean4export` NDJSON stream.
///
/// The first record must be metadata for format 3.1.0. All subsequent records
/// are validated in stream order; name, level, and expression indices must be
/// dense and may only refer backward. Declarations enter a private staging
/// kernel only through its checked admission gates. The kernel is published in
/// [`CompletedImport`] only after every delivered record succeeds and the
/// reader reaches EOF. The upstream format has no footer; EOF alone does not
/// authenticate a record-boundary prefix as the producer's intended artifact.
///
/// # Errors
///
/// Returns [`ImportError`] for I/O, resource, syntax, topology, unsupported
/// profile, or independent-kernel admission failures.
pub fn import_ndjson<R: BufRead>(
    reader: R,
    limits: ImportLimits,
) -> Result<CompletedImport, ImportError> {
    let mut kernel = Kernel::new();
    let report = import_into_staging_kernel(reader, &mut kernel, limits)?;
    Ok(CompletedImport { kernel, report })
}

/// Whether `import_statement_ndjson`'s trusted-declaration gate must let
/// `name` (of kind `kind`) through despite being an otherwise-trusted kind.
///
/// The **only** way through is: the declaration is structurally a `Theorem`
/// (never an `Axiom`, `Opaque`, or `Quotient` — those can never be exempted,
/// no matter what `substituted_theorems` claims) *and* its exact name is one
/// this import actually recorded reconstructing itself, in
/// `report.substituted_theorems` — never a name the untrusted stream merely
/// happens to share with the fixed substitution list
/// (`trusted_substitution::SUBSTITUTABLE_THEOREMS`), since that list is
/// consulted only inside the reconstruction attempt, never here.
fn is_exempted_trusted_declaration(
    kind: DeclarationKind,
    name: &str,
    substituted_theorems: &[String],
) -> bool {
    kind == DeclarationKind::Theorem && substituted_theorems.iter().any(|n| n == name)
}

#[cfg(test)]
mod statement_isolation_tests {
    use super::{DeclarationKind, is_exempted_trusted_declaration};

    #[test]
    fn a_reconstructed_theorem_is_exempted() {
        let substituted = vec!["congrArg".to_owned(), "mt".to_owned()];
        assert!(is_exempted_trusted_declaration(
            DeclarationKind::Theorem,
            "congrArg",
            &substituted
        ));
    }

    #[test]
    fn a_theorem_absent_from_the_substituted_list_is_never_exempted() {
        let substituted = vec!["congrArg".to_owned()];
        assert!(!is_exempted_trusted_declaration(
            DeclarationKind::Theorem,
            "congr",
            &substituted
        ));
    }

    #[test]
    fn an_empty_substituted_list_exempts_nothing() {
        assert!(!is_exempted_trusted_declaration(
            DeclarationKind::Theorem,
            "congrArg",
            &[]
        ));
    }

    /// `propext` is a genuine axiom. Even if it somehow ended up listed in
    /// `substituted_theorems` (a bug this test exists to catch, not a case
    /// the real reconstruction path can produce — see
    /// `trusted_substitution::reconstruct`, which never returns `Ok(Some(_))`
    /// for a name outside `SUBSTITUTABLE_THEOREMS`), the *kind* check alone
    /// must still refuse it: `propext`'s `DeclarationKind` is `Axiom`, never
    /// `Theorem`.
    #[test]
    fn an_axiom_is_never_exempted_regardless_of_the_substituted_list() {
        let substituted = vec!["propext".to_owned()];
        assert!(!is_exempted_trusted_declaration(
            DeclarationKind::Axiom,
            "propext",
            &substituted
        ));
    }

    #[test]
    fn opaque_and_quotient_are_never_exempted() {
        let substituted = vec!["congrArg".to_owned()];
        assert!(!is_exempted_trusted_declaration(
            DeclarationKind::Opaque,
            "congrArg",
            &substituted
        ));
        assert!(!is_exempted_trusted_declaration(
            DeclarationKind::Quotient,
            "congrArg",
            &substituted
        ));
    }
}

/// Import one proof-free statement stream and publish its checked target
/// proposition as a goal.
///
/// The target must be the sole declaration with `target`'s rendered name, must
/// be a non-universe-polymorphic transparent definition, and its definition
/// value must independently infer to `Prop`. The entire stream is rejected if
/// it contains an axiom, theorem, opaque declaration, or quotient primitive —
/// unless that declaration is one of a small, fixed, reviewed set this crate
/// reconstructs and independently kernel-checks itself (see
/// `trusted_substitution`); this prevents a statement adapter from smuggling
/// either the target answer or an unrelated trusted assumption into the
/// producer environment.
///
/// # Errors
///
/// Returns [`StatementImportError`] for any ordinary wire/import failure or
/// violation of the stronger proof-isolation contract.
pub fn import_statement_ndjson<R: BufRead>(
    reader: R,
    limits: ImportLimits,
    target: &str,
) -> Result<CompletedStatementImport, StatementImportError> {
    let mut kernel = Kernel::new();
    let report = import_into_staging_kernel_with_trusted_substitution(reader, &mut kernel, limits)?;

    for identity in &report.declaration_identities {
        if is_exempted_trusted_declaration(
            identity.kind,
            &identity.name,
            &report.substituted_theorems,
        ) {
            continue;
        }
        if matches!(
            identity.kind,
            DeclarationKind::Axiom
                | DeclarationKind::Theorem
                | DeclarationKind::Opaque
                | DeclarationKind::Quotient
        ) {
            return Err(StatementImportError::TrustedDeclaration {
                name: identity.name.clone(),
                kind: identity.kind,
            });
        }
    }

    finish_statement_import(kernel, report, target)
}

/// Import a proof-free target together with an explicit checked candidate set.
///
/// This is the theorem-composition counterpart to [`import_statement_ndjson`].
/// The target remains a transparent `definition : Prop`, so it contributes no
/// proof. A proof-bearing declaration is accepted only when its exact rendered
/// name occurs in `candidate_declarations` (or when it is one of the fixed,
/// independently reconstructed substitutions). Every candidate must exist
/// exactly once and have an empty kernel-measured axiom footprint.
///
/// Importing a candidate does not make it applicable. The untrusted producer
/// must still receive the same explicit names, construct a term, and submit it
/// to the kernel. It never scans the imported environment.
///
/// # Errors
///
/// Returns [`StatementImportError`] for ordinary import failures, a target that
/// is not proof-free, an unlisted trusted declaration, candidate identity
/// drift, or an assumption-bearing candidate.
pub fn import_candidate_statement_ndjson<R: BufRead>(
    reader: R,
    limits: ImportLimits,
    target: &str,
    candidate_declarations: &[String],
) -> Result<CompletedStatementImport, StatementImportError> {
    let mut allowed = candidate_declarations.to_vec();
    allowed.sort();
    allowed.dedup();
    if allowed.len() != candidate_declarations.len() {
        return Err(StatementImportError::DuplicateCandidate);
    }
    if allowed.iter().any(|name| name == target) {
        return Err(StatementImportError::CandidateIsTarget {
            target: target.to_owned(),
        });
    }

    let mut kernel = Kernel::new();
    let report = import_into_staging_kernel_with_trusted_substitution(reader, &mut kernel, limits)?;
    let mut allowed_closure = Vec::new();
    for candidate in &allowed {
        let matches = kernel
            .environment()
            .iter()
            .filter(|(name, _)| kernel.display_name(**name).to_string() == *candidate)
            .map(|(name, _)| *name)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(StatementImportError::CandidateCardinality {
                candidate: candidate.clone(),
                observed: matches.len(),
            });
        }
        let footprint = kernel.axiom_footprint(matches[0]);
        if !footprint.is_empty() {
            return Err(StatementImportError::CandidateHasAxioms {
                candidate: candidate.clone(),
                observed: footprint.len(),
            });
        }
        allowed_closure.push(candidate.clone());
        allowed_closure.extend(
            kernel
                .declaration_dependency_closure(matches[0])
                .into_iter()
                .map(|name| kernel.display_name(name).to_string()),
        );
    }
    allowed_closure.sort();
    allowed_closure.dedup();
    for identity in &report.declaration_identities {
        if is_exempted_trusted_declaration(
            identity.kind,
            &identity.name,
            &report.substituted_theorems,
        ) {
            continue;
        }
        let listed_theorem = identity.kind == DeclarationKind::Theorem
            && allowed_closure.binary_search(&identity.name).is_ok();
        if !listed_theorem
            && matches!(
                identity.kind,
                DeclarationKind::Axiom
                    | DeclarationKind::Theorem
                    | DeclarationKind::Opaque
                    | DeclarationKind::Quotient
            )
        {
            return Err(StatementImportError::TrustedDeclaration {
                name: identity.name.clone(),
                kind: identity.kind,
            });
        }
    }
    finish_statement_import(kernel, report, target)
}

fn finish_statement_import(
    mut kernel: Kernel,
    report: ImportReport,
    target: &str,
) -> Result<CompletedStatementImport, StatementImportError> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter(|(name, _)| kernel.display_name(**name).to_string() == target)
        .map(|(name, declaration)| (*name, declaration.clone()))
        .collect();
    if matches.len() != 1 {
        return Err(StatementImportError::TargetCardinality {
            target: target.to_owned(),
            observed: matches.len(),
        });
    }
    let (target_name, declaration) = &matches[0];
    let Declaration::Definition { uparams, value, .. } = declaration else {
        let kind = report
            .declaration_identities
            .iter()
            .find(|identity| identity.name == target)
            .map(|identity| identity.kind)
            .ok_or_else(|| StatementImportError::TargetCardinality {
                target: target.to_owned(),
                observed: 0,
            })?;
        return Err(StatementImportError::TargetNotDefinition {
            target: target.to_owned(),
            kind,
        });
    };
    if !uparams.is_empty() {
        return Err(StatementImportError::TargetUniverseParameters {
            target: target.to_owned(),
            observed: uparams.len(),
        });
    }
    let goal = *value;
    let inferred = kernel
        .infer(goal)
        .map_err(|_| StatementImportError::GoalNotProp {
            target: target.to_owned(),
        })?;
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);
    if !kernel.def_eq(inferred, prop) {
        return Err(StatementImportError::GoalNotProp {
            target: target.to_owned(),
        });
    }
    Ok(CompletedStatementImport {
        kernel,
        report,
        target_name: *target_name,
        goal,
    })
}

/// Read and translate one stream, recording every **kernel decline** instead of
/// stopping at the first one — a *diagnostic* pass, never an admission path.
///
/// [`import_ndjson`] is fail-closed by design, so on a stream the kernel cannot
/// fully check it reports exactly one blocker and stops. That makes it the wrong
/// instrument for sizing the remaining gap: at a 13/40 admission rate the first
/// decline hides every later one. This pass answers the different question
/// "which declarations does the trusted gate refuse, and why".
///
/// The distinction that keeps this sound: a declined declaration is **skipped,
/// never admitted**. The staging kernel therefore still contains only fully
/// checked declarations, and any later declaration that referred to a skipped
/// one is itself declined with [`KernelError::UnknownConst`] — a *cascade*, which
/// [`CensusReport::declines`] leaves visible for the caller to separate from a
/// root cause. Nothing is published: this function returns counts only, never a
/// [`Kernel`] or a [`CompletedImport`], so no caller can mistake a censused
/// stream for an imported one.
///
/// Only [`ImportError::Kernel`] is recoverable here. I/O, resource, syntax,
/// topology, and unsupported-profile errors remain fatal exactly as in
/// [`import_ndjson`]: those say the bytes were not understood, and continuing
/// past them would census a stream we did not read.
///
/// # Errors
///
/// Returns [`ImportError`] for I/O, resource, syntax, topology, or
/// unsupported-profile failures. Kernel declines are reported in the census
/// rather than returned.
pub fn census_ndjson<R: BufRead>(
    reader: R,
    limits: ImportLimits,
) -> Result<CensusReport, ImportError> {
    let mut kernel = Kernel::new();
    census_into_staging_kernel(reader, &mut kernel, limits)
}

/// One kernel decline, with whatever the caller's inspector computed from the
/// staging kernel that produced it. See [`probe_first_decline`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProbedDecline<T> {
    /// One-based line number of the declaration record.
    pub line: usize,
    /// Rendered declaration name, or `quotient package` for the quotient gate.
    pub declaration: String,
    /// [`KernelError`] variant name — the same cluster key [`census_ndjson`] uses.
    pub code: String,
    /// Full rejection detail, for triage.
    pub detail: String,
    /// The inspector's result.
    pub inspected: T,
}

/// Diagnostic: drive a stream through the trusted gate and, at the **first**
/// kernel decline, hand `inspect` the staging kernel together with the exact
/// [`KernelError`] that refused the record.
///
/// [`census_ndjson`] answers *which* declarations are refused and *why* by
/// variant, but a [`KernelError::TypeMismatch`] carries two [`ExprId`]s and an
/// arena index is not a diagnosis. Sizing a missing definitional-equality rule
/// needs the two *terms*, reduced side by side in the very environment that
/// rejected them — which cannot be reconstructed after the fact, because the
/// staging kernel is dropped.
///
/// **Nothing is published and nothing is admitted.** The refused declaration is
/// not in the kernel the inspector sees; this function returns no [`Kernel`] and
/// no [`CompletedImport`], and after the hook runs the stream fails closed
/// exactly as [`import_ndjson`] would. The higher-ranked bound on `inspect`
/// means the borrow cannot outlive the call, so a caller cannot smuggle the
/// staging kernel out and mistake it for an imported one.
///
/// Returns `Ok(None)` when the stream had no kernel decline at all — i.e. it
/// would have imported cleanly.
///
/// # Errors
///
/// Returns [`ImportError`] for I/O, resource, syntax, topology, or
/// unsupported-profile failures, exactly as [`census_ndjson`] does. A kernel
/// decline is *not* an error here: it is the result.
pub fn probe_first_decline<R, F, T>(
    reader: R,
    limits: ImportLimits,
    inspect: F,
) -> Result<Option<ProbedDecline<T>>, ImportError>
where
    R: BufRead,
    F: for<'k> FnOnce(&'k mut Kernel, &KernelError) -> T,
{
    let mut kernel = Kernel::new();
    let mut captured: Option<ProbedDecline<T>> = None;
    let mut inspect = Some(inspect);
    let outcome = {
        let mut hook =
            |kernel: &mut Kernel, line: usize, declaration: &str, error: &KernelError| {
                let Some(inspect) = inspect.take() else {
                    return;
                };
                captured = Some(ProbedDecline {
                    line,
                    declaration: declaration.to_owned(),
                    code: kernel_error_code(error),
                    detail: format!("{error:?}"),
                    inspected: inspect(kernel, error),
                });
            };
        drive_stream(reader, &mut kernel, limits, None, Some(&mut hook), false)
    };
    match outcome {
        Ok(_) => Ok(captured),
        // The hook fired and then the stream failed closed on that very record,
        // which is the expected path: report the decline rather than the error.
        Err(ImportError::Kernel { .. }) if captured.is_some() => Ok(captured),
        Err(error) => Err(error),
    }
}

/// One declaration record the trusted gate refused during a [`census_ndjson`]
/// pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CensusDecline {
    /// One-based line number of the declaration record.
    pub line: usize,
    /// Rendered declaration name, or `quotient package` for the quotient gate.
    pub declaration: String,
    /// [`KernelError`] variant name — a stable cluster key.
    pub code: String,
    /// Full rejection detail, for triage.
    pub detail: String,
}

/// Counts and per-declaration declines from a [`census_ndjson`] pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CensusReport {
    /// Export-format version from the first record.
    pub format_version: String,
    /// Official Lean version recorded by the exporter.
    pub lean_version: String,
    /// Number of exported declaration records seen.
    pub declaration_records: usize,
    /// Number of declaration records that did not decline. A quotient package
    /// arrives as four records but is gated once, so its first three records
    /// count here even though only the fourth could have been refused.
    pub admitted_records: usize,
    /// Number of kernel declarations in the staging environment at EOF. An
    /// inductive group contributes its family, constructors, and recursor.
    pub admitted_declarations: usize,
    /// Every refused record, in stream order.
    pub declines: Vec<CensusDecline>,
}

fn census_into_staging_kernel<R: BufRead>(
    reader: R,
    kernel: &mut Kernel,
    limits: ImportLimits,
) -> Result<CensusReport, ImportError> {
    let mut declines = Vec::new();
    let report = drive_stream(reader, kernel, limits, Some(&mut declines), None, false)?;
    Ok(CensusReport {
        format_version: report.format_version,
        lean_version: report.lean_version,
        declaration_records: report.declaration_records,
        admitted_records: report.declaration_records - declines.len(),
        admitted_declarations: report.admitted_declarations,
        declines,
    })
}

/// The `KernelError` variant name, used as the census cluster key. `KernelError`
/// is `#[non_exhaustive]`-in-spirit (fifty-plus variants owned by another crate),
/// so this reads the leading identifier of the `Debug` rendering rather than
/// matching exhaustively — a match here would be a maintenance trap that fails
/// closed on the wrong side, turning a new kernel error into a compile break in
/// a diagnostic tool.
fn kernel_error_code(error: &KernelError) -> String {
    let rendered = format!("{error:?}");
    rendered
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect()
}

fn import_into_staging_kernel<R: BufRead>(
    reader: R,
    kernel: &mut Kernel,
    limits: ImportLimits,
) -> Result<ImportReport, ImportError> {
    drive_stream(reader, kernel, limits, None, None, false)
}

/// As [`import_into_staging_kernel`], but with the fixed, reviewed
/// `congrArg`/`congr`/`mt` substitution enabled. Used only by
/// [`import_statement_ndjson`]'s stronger proof-isolation contract; never by
/// ordinary [`import_ndjson`].
fn import_into_staging_kernel_with_trusted_substitution<R: BufRead>(
    reader: R,
    kernel: &mut Kernel,
    limits: ImportLimits,
) -> Result<ImportReport, ImportError> {
    drive_stream(reader, kernel, limits, None, None, true)
}

/// Apply one record's outcome. Without a census sink every error is fatal — the
/// fail-closed contract. With one, and only for [`ImportError::Kernel`], the
/// refusal is recorded and the declaration is skipped; the staging kernel is
/// therefore still made only of declarations the trusted gate accepted.
///
/// `inspect`, when present, is called on the **first** kernel decline with the
/// staging kernel and the exact [`KernelError`]. It is a diagnostic hook only:
/// it cannot admit anything, and it runs before the census/fail-closed decision
/// so it sees the same state either way.
fn record_outcome(
    state: &mut ImportState<'_>,
    outcome: Result<(), ImportError>,
    census: Option<&mut Vec<CensusDecline>>,
    inspect: Option<&mut DeclineInspector<'_>>,
) -> Result<(), ImportError> {
    let outcome = match (outcome, inspect) {
        (
            Err(ImportError::Kernel {
                line,
                declaration,
                source,
            }),
            Some(inspect),
        ) => {
            inspect(state.kernel, line, &declaration, &source);
            Err(ImportError::Kernel {
                line,
                declaration,
                source,
            })
        }
        (outcome, _) => outcome,
    };
    match (outcome, census) {
        (Ok(()), _) => Ok(()),
        (
            Err(ImportError::Kernel {
                line,
                declaration,
                source,
            }),
            Some(declines),
        ) => {
            declines.push(CensusDecline {
                line,
                code: kernel_error_code(&source),
                detail: format!("{source:?}"),
                declaration,
            });
            // A refused quotient package must not leave its four buffered
            // declarations behind, or the next `quot` record reports a spurious
            // length error instead of its own.
            state.reset_pending_quotient();
            Ok(())
        }
        (Err(error), _) => Err(error),
    }
}

/// Diagnostic hook invoked with the staging kernel at a decline.
type DeclineInspector<'a> = dyn FnMut(&mut Kernel, usize, &str, &KernelError) + 'a;

fn drive_stream<R: BufRead>(
    mut reader: R,
    kernel: &mut Kernel,
    limits: ImportLimits,
    mut census: Option<&mut Vec<CensusDecline>>,
    mut inspect: Option<&mut DeclineInspector<'_>>,
    trusted_substitution: bool,
) -> Result<ImportReport, ImportError> {
    if limits.max_line_bytes == 0 || limits.max_records == 0 {
        return Err(malformed(0, "import limits must be nonzero"));
    }
    let mut record_count = 0usize;
    let mut line_bytes = Vec::new();
    let mut metadata: Option<Metadata> = None;
    let mut state = ImportState::new(kernel, trusted_substitution);
    loop {
        line_bytes.clear();
        let read = {
            let mut limited = reader
                .by_ref()
                .take(u64::try_from(limits.max_line_bytes).unwrap_or(u64::MAX) + 1);
            limited.read_until(b'\n', &mut line_bytes)?
        };
        if read == 0 {
            break;
        }
        let line = record_count + 1;
        if read > limits.max_line_bytes {
            return Err(ImportError::LineLimit {
                line,
                limit: limits.max_line_bytes,
            });
        }
        record_count += 1;
        if record_count > limits.max_records {
            return Err(ImportError::RecordLimit {
                limit: limits.max_records,
            });
        }
        if line_bytes.last() == Some(&b'\n') {
            line_bytes.pop();
            if line_bytes.last() == Some(&b'\r') {
                line_bytes.pop();
            }
        }
        if line_bytes.is_empty() {
            return Err(malformed(line, "blank line is not an NDJSON record"));
        }
        let value: Value =
            serde_json::from_slice(&line_bytes).map_err(|error| ImportError::Json {
                line,
                message: error.to_string(),
            })?;
        let record = object(&value, line, "record")?;
        if line == 1 {
            metadata = Some(parse_metadata(record, line)?);
        } else {
            if record.contains_key("meta") {
                return Err(malformed(line, "duplicate metadata record"));
            }
            let outcome = state.import_record(record, line);
            record_outcome(
                &mut state,
                outcome,
                census.as_deref_mut(),
                inspect.as_deref_mut(),
            )?;
        }
    }
    let metadata = metadata.ok_or_else(|| malformed(1, "empty stream; metadata is required"))?;
    state.finish(record_count)?;
    let (axiom_identities, declaration_identities) = if census.is_some() {
        // Diagnostic pass: nothing is published, so there is nothing to
        // identify. Skipping the manifest also keeps a population-scale census
        // from paying for hashes no caller can consume.
        (Vec::new(), Vec::new())
    } else {
        build_identity_manifest(state.kernel).map_err(|message| {
            malformed(
                record_count,
                format!("completed declaration identity manifest: {message}"),
            )
        })?
    };
    Ok(ImportReport {
        format_version: metadata.format_version,
        lean_version: metadata.lean_version,
        lean_githash: metadata.lean_githash,
        exporter_version: metadata.exporter_version,
        names: state.names.len() - 1,
        levels: state.levels.len() - 1,
        expressions: state.expressions.len(),
        declaration_records: state.declaration_records,
        admitted_declarations: state.kernel.environment().len(),
        axioms: state.axioms,
        identity_version: IDENTITY_VERSION,
        axiom_identities,
        declaration_identities,
        substituted_theorems: state.substituted_theorems,
    })
}

const fn quotient_kind_name(kind: QuotKind) -> &'static str {
    match kind {
        QuotKind::Type => "type",
        QuotKind::Ctor => "ctor",
        QuotKind::Lift => "lift",
        QuotKind::Ind => "ind",
    }
}

#[derive(Debug)]
struct Metadata {
    format_version: String,
    lean_version: String,
    lean_githash: String,
    exporter_version: String,
}

fn parse_metadata(record: &Map<String, Value>, line: usize) -> Result<Metadata, ImportError> {
    exact_keys(record, &["meta"], line, "metadata record")?;
    let meta = object(required(record, "meta", line)?, line, "meta")?;
    exact_keys(meta, &["exporter", "lean", "format"], line, "meta")?;
    let exporter = object(required(meta, "exporter", line)?, line, "meta.exporter")?;
    exact_keys(exporter, &["name", "version"], line, "meta.exporter")?;
    if string(
        required(exporter, "name", line)?,
        line,
        "meta.exporter.name",
    )? != "lean4export"
    {
        return Err(malformed(line, "meta.exporter.name is not lean4export"));
    }
    let format = object(required(meta, "format", line)?, line, "meta.format")?;
    exact_keys(format, &["version"], line, "meta.format")?;
    let format_version = string(
        required(format, "version", line)?,
        line,
        "meta.format.version",
    )?;
    if format_version != FORMAT_VERSION {
        return Err(unsupported(line, "format-version"));
    }
    let lean = object(required(meta, "lean", line)?, line, "meta.lean")?;
    exact_keys(lean, &["githash", "version"], line, "meta.lean")?;
    Ok(Metadata {
        format_version: format_version.to_owned(),
        lean_version: string(required(lean, "version", line)?, line, "meta.lean.version")?
            .to_owned(),
        lean_githash: string(required(lean, "githash", line)?, line, "meta.lean.githash")?
            .to_owned(),
        exporter_version: string(
            required(exporter, "version", line)?,
            line,
            "meta.exporter.version",
        )?
        .to_owned(),
    })
}

fn reducibility_hint(raw: &Value, line: usize) -> Result<ReducibilityHint, ImportError> {
    if let Some(value) = raw.as_str() {
        return match value {
            "opaque" => Ok(ReducibilityHint::Opaque),
            "abbrev" => Ok(ReducibilityHint::Abbrev),
            _ => Err(malformed(line, "def.hints: unknown string hint")),
        };
    }
    let value = object(raw, line, "def.hints")?;
    exact_keys(value, &["regular"], line, "def.hints")?;
    let height = u64_value(required(value, "regular", line)?, line, "def.hints.regular")?;
    let height = u16::try_from(height)
        .map_err(|_| malformed(line, "def.hints.regular exceeds kernel width"))?;
    Ok(ReducibilityHint::Regular(height))
}

fn binder_info(raw: &Value, line: usize) -> Result<BinderInfo, ImportError> {
    match string(raw, line, "binderInfo")? {
        "default" => Ok(BinderInfo::Default),
        "implicit" => Ok(BinderInfo::Implicit),
        "strictImplicit" => Ok(BinderInfo::StrictImplicit),
        "instImplicit" => Ok(BinderInfo::InstImplicit),
        _ => Err(malformed(line, "binderInfo: unknown binder mode")),
    }
}

fn required<'value>(
    object: &'value Map<String, Value>,
    key: &str,
    line: usize,
) -> Result<&'value Value, ImportError> {
    object
        .get(key)
        .ok_or_else(|| malformed(line, format!("missing required field {key}")))
}

fn exact_keys(
    object: &Map<String, Value>,
    keys: &[&str],
    line: usize,
    field: &str,
) -> Result<(), ImportError> {
    if object.len() == keys.len() && keys.iter().all(|key| object.contains_key(*key)) {
        return Ok(());
    }
    let mut actual: Vec<_> = object.keys().cloned().collect();
    actual.sort();
    Err(malformed(
        line,
        format!("{field}: expected fields {keys:?}, got {actual:?}"),
    ))
}

fn object<'value>(
    raw: &'value Value,
    line: usize,
    field: &str,
) -> Result<&'value Map<String, Value>, ImportError> {
    raw.as_object()
        .ok_or_else(|| malformed(line, format!("{field}: expected object")))
}

fn array<'value>(
    raw: &'value Value,
    line: usize,
    field: &str,
) -> Result<&'value [Value], ImportError> {
    raw.as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| malformed(line, format!("{field}: expected array")))
}

fn string<'value>(
    raw: &'value Value,
    line: usize,
    field: &str,
) -> Result<&'value str, ImportError> {
    raw.as_str()
        .ok_or_else(|| malformed(line, format!("{field}: expected string")))
}

fn boolean(raw: &Value, line: usize, field: &str) -> Result<bool, ImportError> {
    raw.as_bool()
        .ok_or_else(|| malformed(line, format!("{field}: expected Boolean")))
}

fn u64_value(raw: &Value, line: usize, field: &str) -> Result<u64, ImportError> {
    raw.as_u64()
        .ok_or_else(|| malformed(line, format!("{field}: expected non-negative integer")))
}

fn usize_value(raw: &Value, line: usize, field: &str) -> Result<usize, ImportError> {
    let value = u64_value(raw, line, field)?;
    usize::try_from(value).map_err(|_| malformed(line, format!("{field}: does not fit usize")))
}

fn index(raw: &Value, line: usize, field: &str) -> Result<usize, ImportError> {
    usize_value(raw, line, field)
}

fn malformed(line: usize, message: impl Into<String>) -> ImportError {
    ImportError::Malformed {
        line,
        message: message.into(),
    }
}

const fn unsupported(line: usize, code: &'static str) -> ImportError {
    ImportError::Unsupported { line, code }
}
