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
//! inductive groups. It translates projections and natural literals and
//! rejects unsupported string literals, quotient packages, unsafe or partial
//! declarations, nested groups, unknown records, and malformed/forward
//! references. Reflexive metadata is descriptive; the independent kernel
//! decides support from the translated terms. [`import_ndjson`] owns a private
//! staging kernel and publishes it only after the complete stream succeeds, so
//! an error cannot expose a partial environment.
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
    NameId, NatLit, RecRule, ReducibilityHint,
};
use serde_json::{Map, Value};

mod identity;

pub use identity::{
    AxiomIdentity, DeclarationDependencyIdentity, DeclarationIdentity, DeclarationKind,
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
/// };
/// let forged = CompletedImport { kernel: Kernel::new(), report };
/// ```
#[derive(Debug)]
pub struct CompletedImport {
    kernel: Kernel,
    report: ImportReport,
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
}

#[derive(Debug)]
struct ExportedInductiveFamily {
    name: NameId,
    uparams: Vec<NameId>,
    ty: ExprId,
    num_params: usize,
    num_indices: usize,
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
    fn new(kernel: &'kernel mut Kernel) -> Self {
        let anonymous = kernel.anon();
        let zero = kernel.level_zero();
        Self {
            kernel,
            names: vec![anonymous],
            levels: vec![zero],
            expressions: Vec::new(),
            declaration_records: 0,
            axioms: Vec::new(),
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
            "strVal" => return Err(unsupported(line, "literal-string-typing")),
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
        self.declaration_records += 1;
        match kinds[0] {
            "axiom" => self.import_axiom(required(record, "axiom", line)?, line),
            "def" => self.import_definition(required(record, "def", line)?, line),
            "opaque" => self.import_opaque(required(record, "opaque", line)?, line),
            "thm" => self.import_theorem(required(record, "thm", line)?, line),
            "quot" => Err(unsupported(line, "quotient-package")),
            "inductive" => self.import_inductive(required(record, "inductive", line)?, line),
            _ => unreachable!(),
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
        let declaration = Declaration::Theorem {
            name: self.name(required(value, "name", line)?, line, "thm.name")?,
            uparams: self.name_array(
                required(value, "levelParams", line)?,
                line,
                "thm.levelParams",
            )?,
            ty: self.expression(required(value, "type", line)?, line, "thm.type")?,
            value: self.expression(required(value, "value", line)?, line, "thm.value")?,
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
        if types.len() == 1 && recursors.len() != 1 {
            return Err(malformed(
                line,
                "single-family inductive must export one recursor",
            ));
        }
        if recursors.len() != types.len() {
            return Err(malformed(
                line,
                "inductive group must export one recursor per family",
            ));
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
        for raw_type in types {
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
            if u64_value(
                required(ty, "numNested", line)?,
                line,
                "inductive.type.numNested",
            )? != 0
            {
                return Err(unsupported(line, "inductive-nested"));
            }
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

        let expected_recursors = exported_families
            .iter()
            .enumerate()
            .map(|(index, family)| (self.kernel.name_str(family.name, "rec"), index))
            .collect::<BTreeMap<_, _>>();
        let mut recursor_records = BTreeMap::new();
        for raw_recursor in recursors {
            let rec = object(raw_recursor, line, "inductive.rec")?;
            let name = self.name(required(rec, "name", line)?, line, "inductive.rec.name")?;
            if !expected_recursors.contains_key(&name) {
                return Err(malformed(
                    line,
                    "exported recursor name does not belong to the group",
                ));
            }
            if recursor_records.insert(name, raw_recursor).is_some() {
                return Err(malformed(line, "inductive group repeats a recursor record"));
            }
        }
        for (recursor_name, family_index) in expected_recursors {
            let raw_recursor = recursor_records
                .get(&recursor_name)
                .ok_or_else(|| malformed(line, "group family recursor record is missing"))?;
            let family = &exported_families[family_index];
            self.validate_generated_recursor(
                raw_recursor,
                family.name,
                family.num_indices,
                &group_names,
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
        inductive: NameId,
        exported_num_indices: usize,
        expected_all: &[NameId],
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
        self.validate_recursor_group_metadata(rec, expected_all, line)?;
        let name = self.name(required(rec, "name", line)?, line, "inductive.rec.name")?;
        let expected_name = self.kernel.name_str(inductive, "rec");
        if name != expected_name {
            return Err(malformed(
                line,
                "exported recursor name is not <inductive>.rec",
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
        let universe_substitution =
            self.recursor_universe_substitution(&exported_uparams, &uparams, line)?;
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
        if usize::from(num_indices) != exported_num_indices {
            return Err(malformed(
                line,
                "generated family index count differs from export",
            ));
        }
        self.validate_rec_rules(
            required(rec, "rules", line)?,
            &rec_rules,
            &universe_substitution,
            line,
        )
    }

    fn validate_recursor_group_metadata(
        &self,
        rec: &Map<String, Value>,
        expected_all: &[NameId],
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
        if expected_all.len() > 1 && is_k_target {
            return Err(malformed(line, "mutual recursor may not be a K target"));
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

    fn validate_rec_rules(
        &mut self,
        raw: &Value,
        generated: &[RecRule],
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

fn import_into_staging_kernel<R: BufRead>(
    mut reader: R,
    kernel: &mut Kernel,
    limits: ImportLimits,
) -> Result<ImportReport, ImportError> {
    if limits.max_line_bytes == 0 || limits.max_records == 0 {
        return Err(malformed(0, "import limits must be nonzero"));
    }
    let mut record_count = 0usize;
    let mut line_bytes = Vec::new();
    let mut metadata: Option<Metadata> = None;
    let mut state = ImportState::new(kernel);
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
            state.import_record(record, line)?;
        }
    }
    let metadata = metadata.ok_or_else(|| malformed(1, "empty stream; metadata is required"))?;
    let (axiom_identities, declaration_identities) = build_identity_manifest(state.kernel)
        .map_err(|message| {
            malformed(
                record_count,
                format!("completed declaration identity manifest: {message}"),
            )
        })?;
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
    })
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
