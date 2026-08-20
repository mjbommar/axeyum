//! Emit an official `lean4export` NDJSON **format 3.1.0** stream from a checked
//! [`Kernel`] environment.
//!
//! This is the mirror of `axeyum-lean-import`, which consumes that same format
//! fail-closed. The two are written against the same external specification and
//! share no code, so re-importing an emitted stream and comparing ADR-0350
//! canonical identity manifests is a genuine differential test rather than a
//! tautology.
//!
//! Unlike [`crate::Kernel::render_lean_module`], this is **not** surface syntax:
//! nothing here is elaborated, no implicit argument is re-inferred, no coercion
//! is inserted and no code is generated. Every declaration is transmitted in the
//! same fully explicit form the kernel checked, which is what an independent
//! kernel (Lean's own `Environment.replay`, Trepplein, nanoda, lean4lean) reads.
//!
//! # Fail closed
//!
//! Every construct this writer cannot represent in format 3.1.0 is a typed
//! [`ExportError`], never a silent omission: a silently skipped declaration
//! would produce a stream whose consumer checks *less* than the kernel did,
//! which is exactly the failure mode an export exists to rule out.
//!
//! # Fidelity notes, measured rather than assumed
//!
//! * `k` (the recursor's K-like reduction flag) is not stored in
//!   [`Declaration::Recursor`], so it is **derived** here by Lean 4.30's own
//!   rule — a `Prop`-valued family with exactly one constructor whose only
//!   arguments are the parameters — and the derivation is checked against every
//!   official v4.30 fixture by the round-trip suite.
//! * `letE.nondep`, `isReflexive`, and `all` for non-mutual definitions are
//!   descriptive wire metadata that the kernel does not model. They are emitted
//!   in their conservative form (`false`, `false`, the declaration's own name).
//!   The importer treats all three as descriptive as well
//!   (`axeyum-lean-import/src/lib.rs:874-880`).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fmt::Write as _;
use std::io;

use crate::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, LevelNode, Lit, NameId, NameNode,
    QuotKind, ReducibilityHint,
};

/// The only `lean4export` wire-format version this writer emits.
pub const EXPORT_FORMAT_VERSION: &str = "3.1.0";

/// Provenance recorded in the stream's metadata record.
///
/// The format's metadata names the Lean release and exporter that produced the
/// declarations. Axeyum is not Lean, so these values are supplied by the caller
/// rather than fabricated: a round-trip of an official export carries the
/// original provenance through unchanged, and an axeyum-produced development
/// says so ([`Lean4ExportMetadata::axeyum`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lean4ExportMetadata {
    /// `meta.lean.version` — the Lean release these declarations target.
    pub lean_version: String,
    /// `meta.lean.githash` — the Lean source hash, or an explicit non-Lean
    /// producer label.
    pub lean_githash: String,
    /// `meta.exporter.version` — the exporter's own version.
    pub exporter_version: String,
}

/// Evidence that root-selected transport erased only checked, canonical
/// `autoParam` annotations from declaration types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutoParamTypeNormalizationReport {
    /// Selected declarations whose type changed, in deterministic name order.
    pub normalized_declarations: Vec<String>,
    /// Unique saturated annotation nodes erased from those declaration types.
    pub rewritten_occurrences: usize,
}

impl Lean4ExportMetadata {
    /// Provenance for a stream produced by this kernel rather than by Lean.
    ///
    /// `lean_githash` is the explicit producer label `axeyum-lean-kernel`, not a
    /// Lean commit: nothing in this stream came from a Lean binary, and a
    /// plausible-looking hash would say otherwise.
    #[must_use]
    pub fn axeyum(lean_version: impl Into<String>) -> Self {
        Self {
            lean_version: lean_version.into(),
            lean_githash: "axeyum-lean-kernel".to_owned(),
            exporter_version: EXPORT_FORMAT_VERSION.to_owned(),
        }
    }
}

/// A kernel construct that format 3.1.0 cannot carry, or an environment this
/// writer refuses to transmit.
#[derive(Debug)]
pub enum ExportError {
    /// The stream could not be written.
    Io(io::Error),
    /// A declaration contains a free variable. Admitted declarations are closed;
    /// a loose `FVar` has no wire representation and is never emitted silently.
    FreeVariable {
        /// The declaration being emitted.
        declaration: String,
    },
    /// A `Recursor` in the environment does not belong to any exported
    /// inductive group under Lean's `I.rec` / `I.rec_<n>` naming.
    UnclaimedRecursor {
        /// The recursor's displayed name.
        name: String,
    },
    /// A `Constructor` in the environment names a parent that is not an
    /// exported `Inductive`.
    UnclaimedConstructor {
        /// The constructor's displayed name.
        name: String,
    },
    /// An inductive group is missing a declaration the kernel must have
    /// generated (a family, a constructor, or a recursor).
    MissingGroupDeclaration {
        /// The missing declaration's displayed name.
        name: String,
    },
    /// The environment holds an incomplete quotient package. The four members
    /// are one atomic unit on the wire.
    IncompleteQuotientPackage {
        /// How many of the four members are present.
        present: usize,
    },
    /// Declaration dependencies do not admit a linear order. Format 3.1.0 is
    /// strictly back-referencing, so a cycle cannot be transmitted.
    DependencyCycle {
        /// The displayed names participating in the cycle, in id order.
        names: Vec<String>,
    },
    /// A count exceeds what the wire format's readers accept.
    CountOutOfRange {
        /// The field whose value does not fit.
        field: &'static str,
    },
    /// A root-selected export was requested without any roots.
    EmptyRoots,
    /// A root-selected export named no declaration in the checked environment.
    MissingRoot {
        /// The rendered root name when one is available in this kernel's name arena.
        name: String,
    },
    /// An explicit theorem-leaf set repeats one declaration.
    DuplicateTheoremLeaf {
        /// Repeated rendered theorem name.
        name: String,
    },
    /// An explicit dependency leaf is not a checked theorem.
    LeafIsNotTheorem {
        /// Rendered non-theorem declaration name.
        name: String,
    },
    /// An explicit theorem leaf is not reachable from the selected roots.
    UnreachableTheoremLeaf {
        /// Rendered unreachable theorem name.
        name: String,
    },
    /// A selected declaration references a constant absent from the environment.
    MissingDependency {
        /// The selected declaration containing the reference.
        declaration: String,
        /// The referenced but undeclared constant.
        dependency: String,
    },
    /// A referenced root `autoParam` declaration does not have Lean 4.30's
    /// canonical elaboration-only abbreviation shape.
    AutoParamContract {
        /// Stable fail-closed diagnostic.
        reason: &'static str,
    },
    /// A canonical annotation rewrite did not preserve the complete source
    /// declaration type by kernel definitional equality.
    AutoParamTypeMismatch {
        /// Declaration whose type failed the equivalence check.
        declaration: String,
    },
}

impl fmt::Display for ExportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(f, "lean4export I/O error: {error}"),
            Self::FreeVariable { declaration } => {
                write!(f, "{declaration}: free variables have no export form")
            }
            Self::UnclaimedRecursor { name } => {
                write!(f, "{name}: recursor belongs to no exported inductive group")
            }
            Self::UnclaimedConstructor { name } => {
                write!(f, "{name}: constructor parent is not an exported inductive")
            }
            Self::MissingGroupDeclaration { name } => {
                write!(f, "{name}: inductive group declaration is missing")
            }
            Self::IncompleteQuotientPackage { present } => write!(
                f,
                "quotient package holds {present} of 4 declarations; it is one atomic record group"
            ),
            Self::DependencyCycle { names } => {
                write!(f, "declaration dependency cycle: {names:?}")
            }
            Self::CountOutOfRange { field } => write!(f, "{field} exceeds the wire format's range"),
            Self::EmptyRoots => write!(f, "root-selected export requires at least one root"),
            Self::MissingRoot { name } => {
                write!(f, "root-selected export has no declaration named {name}")
            }
            Self::DuplicateTheoremLeaf { name } => {
                write!(f, "target theorem leaf is repeated: {name}")
            }
            Self::LeafIsNotTheorem { name } => {
                write!(f, "target dependency leaf is not a theorem: {name}")
            }
            Self::UnreachableTheoremLeaf { name } => {
                write!(
                    f,
                    "target theorem leaf is unreachable from the roots: {name}"
                )
            }
            Self::MissingDependency {
                declaration,
                dependency,
            } => write!(
                f,
                "{declaration}: referenced constant {dependency} is absent from the environment"
            ),
            Self::AutoParamContract { reason } => {
                write!(f, "autoParam normalization contract failed: {reason}")
            }
            Self::AutoParamTypeMismatch { declaration } => write!(
                f,
                "autoParam normalization changed declaration type {declaration}"
            ),
        }
    }
}

impl std::error::Error for ExportError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for ExportError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// Depth-first traversal state for the unit topological sort.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mark {
    Unvisited,
    OnStack,
    Done,
}

/// One emission unit: a record group that must be transmitted atomically.
#[derive(Debug, Clone)]
enum Unit {
    /// A single non-inductive declaration.
    Single(NameId),
    /// One ordered inductive group: its families, their constructors, and the
    /// kernel-generated recursors.
    Inductive(InductiveUnit),
    /// The privileged four-member quotient package, in canonical order.
    Quotient(Vec<NameId>),
}

#[derive(Debug, Clone)]
struct InductiveUnit {
    families: Vec<NameId>,
    constructors: Vec<NameId>,
    recursors: Vec<NameId>,
}

#[derive(Debug, Clone, Copy)]
struct NormalizedType {
    expression: ExprId,
    rewritten_occurrences: usize,
}

#[derive(Debug, Default)]
struct TransportNormalization {
    types: BTreeMap<NameId, NormalizedType>,
    recursor_rules: BTreeMap<(NameId, usize), NormalizedType>,
}

impl Unit {
    fn members(&self) -> Vec<NameId> {
        match self {
            Self::Single(name) => vec![*name],
            Self::Inductive(unit) => unit
                .families
                .iter()
                .chain(&unit.constructors)
                .chain(&unit.recursors)
                .copied()
                .collect(),
            Self::Quotient(names) => names.clone(),
        }
    }

    fn key(&self) -> NameId {
        match self {
            Self::Single(name) => *name,
            Self::Inductive(unit) => unit.families[0],
            Self::Quotient(names) => names[0],
        }
    }
}

impl Kernel {
    /// Render the complete checked environment as an official `lean4export`
    /// NDJSON 3.1.0 stream.
    ///
    /// Declarations are emitted in a deterministic dependency order: every
    /// constant is declared before it is referenced, inductive groups and the
    /// quotient package travel as single atomic record groups, and name, level,
    /// and expression indices are dense and strictly back-referencing.
    ///
    /// # Errors
    ///
    /// Returns [`ExportError`] for any construct the format cannot carry (see
    /// the variants), never a silently truncated stream.
    pub fn render_lean4export_ndjson(
        &self,
        metadata: &Lean4ExportMetadata,
    ) -> Result<String, ExportError> {
        let mut buffer = Vec::new();
        self.write_lean4export_ndjson(&mut buffer, metadata)?;
        // Every byte written by this module is ASCII-escaped JSON plus the
        // interned name components, which are already valid UTF-8.
        String::from_utf8(buffer).map_err(|error| {
            ExportError::Io(io::Error::new(
                io::ErrorKind::InvalidData,
                error.to_string(),
            ))
        })
    }

    /// Render only the checked declaration closure of `roots` as an official
    /// `lean4export` NDJSON 3.1.0 stream.
    ///
    /// Reachability follows every selected declaration's type, value, and
    /// recursor reduction rules. Inductive families and the quotient package
    /// remain atomic emission units, so selecting one member retains the whole
    /// checked package. Unrelated declarations are absent from the stream and
    /// therefore unavailable to its consumer.
    ///
    /// This is an environmental isolation primitive, not a proof-dependency
    /// eraser: if a selected definition's body references a theorem or axiom,
    /// that trusted declaration is selected too.
    ///
    /// # Errors
    ///
    /// Returns [`ExportError::EmptyRoots`] for an empty root set,
    /// [`ExportError::MissingRoot`] for a name absent from the environment, or
    /// any ordinary export error from the selected closure.
    pub fn render_lean4export_ndjson_roots(
        &self,
        metadata: &Lean4ExportMetadata,
        roots: &[NameId],
    ) -> Result<String, ExportError> {
        let mut buffer = Vec::new();
        self.write_lean4export_ndjson_roots(&mut buffer, metadata, roots)?;
        String::from_utf8(buffer).map_err(|error| {
            ExportError::Io(io::Error::new(
                io::ErrorKind::InvalidData,
                error.to_string(),
            ))
        })
    }

    /// Return the exact atomic declaration closure root-selected export would
    /// transport, in deterministic dependency order.
    ///
    /// This includes complete inductive and quotient units, recursor reduction
    /// rules, and implicit literal bootstrap dependencies. It is the read-only
    /// authority for deciding whether a prospective producer environment would
    /// retain a trusted declaration.
    ///
    /// # Errors
    ///
    /// Returns the same typed root, package, missing-dependency, or cycle errors
    /// as [`Self::render_lean4export_ndjson_roots`].
    pub fn root_declaration_closure(&self, roots: &[NameId]) -> Result<Vec<NameId>, ExportError> {
        let normalization = TransportNormalization::default();
        let units = self.select_root_units(self.export_units()?, roots, &normalization)?;
        let order = self.order_units(units, &normalization)?;
        Ok(order.into_iter().flat_map(|unit| unit.members()).collect())
    }

    /// Return an atomic root closure that stops at explicit checked theorem
    /// leaves while retaining every declaration referenced by each leaf's type.
    ///
    /// This is the source-side graph primitive for target-owned theorem reuse:
    /// a caller may recheck a same-name target theorem's type and then avoid
    /// transporting the unrelated source proof behind it. Leaves must be
    /// unique checked theorems and reachable from `roots`; an unused proposed
    /// cut is rejected rather than recorded as if it changed the closure.
    ///
    /// # Errors
    ///
    /// Returns the ordinary root/package/dependency errors plus a typed decline
    /// for a duplicate, missing, non-theorem, or unreachable leaf.
    pub fn root_declaration_closure_with_theorem_leaves(
        &self,
        roots: &[NameId],
        theorem_leaves: &[NameId],
    ) -> Result<Vec<NameId>, ExportError> {
        let mut leaves = BTreeSet::new();
        for &leaf in theorem_leaves {
            let rendered = self.display_name(leaf).to_string();
            let Some(declaration) = self.environment().get(leaf) else {
                return Err(ExportError::MissingRoot { name: rendered });
            };
            if !matches!(declaration, Declaration::Theorem { .. }) {
                return Err(ExportError::LeafIsNotTheorem { name: rendered });
            }
            if !leaves.insert(leaf) {
                return Err(ExportError::DuplicateTheoremLeaf { name: rendered });
            }
        }
        let normalization = TransportNormalization::default();
        let units = self.select_root_units_with_theorem_leaves(
            self.export_units()?,
            roots,
            &normalization,
            &leaves,
        )?;
        let order = self.order_units_with_theorem_leaves(units, &normalization, &leaves)?;
        let closure = order
            .into_iter()
            .flat_map(|unit| unit.members())
            .collect::<Vec<_>>();
        for &leaf in &leaves {
            if !closure.contains(&leaf) {
                return Err(ExportError::UnreachableTheoremLeaf {
                    name: self.display_name(leaf).to_string(),
                });
            }
        }
        Ok(closure)
    }

    /// Return the atomic root closure after checked removal of canonical,
    /// saturated `autoParam` annotations from declaration types.
    ///
    /// The source kernel independently checks every changed complete
    /// declaration type against its normalized form. Definition values,
    /// recursor rules, partial applications, and other annotations remain
    /// exact.
    ///
    /// # Errors
    ///
    /// Returns [`ExportError::AutoParamContract`] for a noncanonical referenced
    /// gadget, [`ExportError::AutoParamTypeMismatch`] for a failed source-kernel
    /// equivalence check, or an ordinary root-export error.
    pub fn root_declaration_closure_checked_auto_param_types(
        &mut self,
        roots: &[NameId],
    ) -> Result<(Vec<NameId>, AutoParamTypeNormalizationReport), ExportError> {
        let normalization = TransportNormalization {
            types: self.checked_auto_param_types()?,
            recursor_rules: BTreeMap::new(),
        };
        let units = self.select_root_units(self.export_units()?, roots, &normalization)?;
        let order = self.order_units(units, &normalization)?;
        let report = self.auto_param_report(&order, &normalization);
        Ok((
            order.into_iter().flat_map(|unit| unit.members()).collect(),
            report,
        ))
    }

    /// Render one atomic root closure after checked type-only `autoParam`
    /// normalization, returning the exact normalization report used by both
    /// dependency selection and emission.
    ///
    /// # Errors
    ///
    /// Returns the typed normalization and ordinary root-export errors
    /// documented by [`Self::root_declaration_closure_checked_auto_param_types`].
    pub fn render_lean4export_ndjson_roots_checked_auto_param_types(
        &mut self,
        metadata: &Lean4ExportMetadata,
        roots: &[NameId],
    ) -> Result<(String, AutoParamTypeNormalizationReport), ExportError> {
        let normalization = TransportNormalization {
            types: self.checked_auto_param_types()?,
            recursor_rules: BTreeMap::new(),
        };
        let units = self.select_root_units(self.export_units()?, roots, &normalization)?;
        let order = self.order_units(units, &normalization)?;
        let report = self.auto_param_report(&order, &normalization);
        let mut buffer = Vec::new();
        self.write_ordered_units(&mut buffer, metadata, &order, &normalization)?;
        let stream = String::from_utf8(buffer).map_err(|error| {
            ExportError::Io(io::Error::new(
                io::ErrorKind::InvalidData,
                error.to_string(),
            ))
        })?;
        Ok((stream, report))
    }

    /// Return the atomic root closure after checked normalization of canonical
    /// `autoParam` annotations in declaration types and recursor-rule binder
    /// domains. Ordinary definition values remain exact.
    ///
    /// # Errors
    ///
    /// Returns the type-only errors plus a typed mismatch if a complete
    /// normalized recursor rule is not definitionally equal to its source.
    pub fn root_declaration_closure_checked_auto_param_binders(
        &mut self,
        roots: &[NameId],
    ) -> Result<(Vec<NameId>, AutoParamTypeNormalizationReport), ExportError> {
        let normalization = self.checked_auto_param_binders()?;
        let units = self.select_root_units(self.export_units()?, roots, &normalization)?;
        let order = self.order_units(units, &normalization)?;
        let report = self.auto_param_report(&order, &normalization);
        Ok((
            order.into_iter().flat_map(|unit| unit.members()).collect(),
            report,
        ))
    }

    /// Render the closure accepted by
    /// [`Self::root_declaration_closure_checked_auto_param_binders`].
    ///
    /// # Errors
    ///
    /// Returns its typed normalization errors or an ordinary export error.
    pub fn render_lean4export_ndjson_roots_checked_auto_param_binders(
        &mut self,
        metadata: &Lean4ExportMetadata,
        roots: &[NameId],
    ) -> Result<(String, AutoParamTypeNormalizationReport), ExportError> {
        let normalization = self.checked_auto_param_binders()?;
        let units = self.select_root_units(self.export_units()?, roots, &normalization)?;
        let order = self.order_units(units, &normalization)?;
        let report = self.auto_param_report(&order, &normalization);
        let mut buffer = Vec::new();
        self.write_ordered_units(&mut buffer, metadata, &order, &normalization)?;
        let stream = String::from_utf8(buffer).map_err(|error| {
            ExportError::Io(io::Error::new(
                io::ErrorKind::InvalidData,
                error.to_string(),
            ))
        })?;
        Ok((stream, report))
    }

    fn checked_auto_param_binders(&mut self) -> Result<TransportNormalization, ExportError> {
        let types = self.checked_auto_param_types()?;
        let anonymous = NameId(0);
        let Some(auto_param) = self.lookup_name_str(anonymous, "autoParam") else {
            return Ok(TransportNormalization {
                types,
                recursor_rules: BTreeMap::new(),
            });
        };
        let rules: Vec<(NameId, usize, ExprId)> = self
            .environment()
            .iter()
            .filter_map(|(&name, declaration)| match declaration {
                Declaration::Recursor { rec_rules, .. } => Some(
                    rec_rules
                        .iter()
                        .enumerate()
                        .map(|(index, rule)| (name, index, rule.value))
                        .collect::<Vec<_>>(),
                ),
                _ => None,
            })
            .flatten()
            .collect();
        let mut recursor_rules = BTreeMap::new();
        for (name, index, source) in rules {
            let mut memo = BTreeMap::new();
            let mut rewritten = BTreeSet::new();
            let normalized = self.normalize_auto_param_binder_annotations(
                source,
                auto_param,
                &mut memo,
                &mut rewritten,
            );
            if normalized == source {
                continue;
            }
            self.validate_auto_param_contract(auto_param)?;
            let source_type =
                self.infer(source)
                    .map_err(|_| ExportError::AutoParamTypeMismatch {
                        declaration: format!("{} rule {index}", self.display_name(name)),
                    })?;
            let normalized_type =
                self.infer(normalized)
                    .map_err(|_| ExportError::AutoParamTypeMismatch {
                        declaration: format!("{} rule {index}", self.display_name(name)),
                    })?;
            if !self.def_eq(source_type, normalized_type) || !self.def_eq(source, normalized) {
                return Err(ExportError::AutoParamTypeMismatch {
                    declaration: format!("{} rule {index}", self.display_name(name)),
                });
            }
            recursor_rules.insert(
                (name, index),
                NormalizedType {
                    expression: normalized,
                    rewritten_occurrences: rewritten.len(),
                },
            );
        }
        Ok(TransportNormalization {
            types,
            recursor_rules,
        })
    }

    fn checked_auto_param_types(
        &mut self,
    ) -> Result<BTreeMap<NameId, NormalizedType>, ExportError> {
        let anonymous = NameId(0);
        let Some(auto_param) = self.lookup_name_str(anonymous, "autoParam") else {
            return Ok(BTreeMap::new());
        };
        let declaration_types: Vec<(NameId, ExprId)> = self
            .environment()
            .iter()
            .filter_map(|(&name, declaration)| {
                (!matches!(declaration, Declaration::Quotient { .. }))
                    .then_some((name, declaration.ty()))
            })
            .collect();
        let referenced = declaration_types
            .iter()
            .any(|&(_, ty)| self.contains_saturated_auto_param(ty, auto_param));
        if !referenced {
            return Ok(BTreeMap::new());
        }
        self.validate_auto_param_contract(auto_param)?;

        let mut normalized_types = BTreeMap::new();
        for (name, source) in declaration_types {
            let mut memo = BTreeMap::new();
            let mut rewritten = BTreeSet::new();
            let normalized =
                self.normalize_auto_param_type(source, auto_param, &mut memo, &mut rewritten);
            if normalized == source {
                continue;
            }
            let source_sort =
                self.infer(source)
                    .map_err(|_| ExportError::AutoParamTypeMismatch {
                        declaration: self.display_name(name).to_string(),
                    })?;
            let normalized_sort =
                self.infer(normalized)
                    .map_err(|_| ExportError::AutoParamTypeMismatch {
                        declaration: self.display_name(name).to_string(),
                    })?;
            if !self.def_eq(source_sort, normalized_sort) || !self.def_eq(source, normalized) {
                return Err(ExportError::AutoParamTypeMismatch {
                    declaration: self.display_name(name).to_string(),
                });
            }
            normalized_types.insert(
                name,
                NormalizedType {
                    expression: normalized,
                    rewritten_occurrences: rewritten.len(),
                },
            );
        }
        Ok(normalized_types)
    }

    fn auto_param_report(
        &self,
        order: &[Unit],
        normalization: &TransportNormalization,
    ) -> AutoParamTypeNormalizationReport {
        let selected: BTreeSet<_> = order.iter().flat_map(Unit::members).collect();
        let mut normalized_declarations: Vec<_> = normalization
            .types
            .iter()
            .filter(|(name, _)| selected.contains(name))
            .map(|(&name, _)| self.display_name(name).to_string())
            .collect();
        normalized_declarations.extend(
            normalization
                .recursor_rules
                .keys()
                .filter(|(name, _)| selected.contains(name))
                .map(|(name, _)| self.display_name(*name).to_string()),
        );
        normalized_declarations.sort();
        normalized_declarations.dedup();
        let rewritten_occurrences = normalization
            .types
            .iter()
            .filter(|(name, _)| selected.contains(name))
            .map(|(_, normalized)| normalized.rewritten_occurrences)
            .chain(
                normalization
                    .recursor_rules
                    .iter()
                    .filter(|((name, _), _)| selected.contains(name))
                    .map(|(_, normalized)| normalized.rewritten_occurrences),
            )
            .sum();
        AutoParamTypeNormalizationReport {
            normalized_declarations,
            rewritten_occurrences,
        }
    }

    fn contains_saturated_auto_param(&self, root: ExprId, auto_param: NameId) -> bool {
        let mut pending = vec![root];
        let mut visited = BTreeSet::new();
        while let Some(expression) = pending.pop() {
            if !visited.insert(expression) {
                continue;
            }
            if self
                .auto_param_type_argument(expression, auto_param)
                .is_some()
            {
                return true;
            }
            match self.expr_node(expression) {
                ExprNode::Proj(_, _, structure) => pending.push(*structure),
                ExprNode::App(function, argument) => {
                    pending.push(*function);
                    pending.push(*argument);
                }
                ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                    pending.push(*ty);
                    pending.push(*body);
                }
                ExprNode::Let(_, ty, value, body) => {
                    pending.push(*ty);
                    pending.push(*value);
                    pending.push(*body);
                }
                ExprNode::BVar(_)
                | ExprNode::FVar(_)
                | ExprNode::Sort(_)
                | ExprNode::Const(..)
                | ExprNode::Lit(_) => {}
            }
        }
        false
    }

    fn auto_param_type_argument(&self, expression: ExprId, auto_param: NameId) -> Option<ExprId> {
        let ExprNode::App(with_type, _) = self.expr_node(expression) else {
            return None;
        };
        let ExprNode::App(head, ty) = self.expr_node(*with_type) else {
            return None;
        };
        matches!(
            self.expr_node(*head),
            ExprNode::Const(name, levels) if *name == auto_param && levels.len() == 1
        )
        .then_some(*ty)
    }

    fn validate_auto_param_contract(&self, auto_param: NameId) -> Result<(), ExportError> {
        let Some(Declaration::Definition {
            uparams,
            ty,
            value,
            hint: ReducibilityHint::Abbrev,
            ..
        }) = self.environment().get(auto_param)
        else {
            return Err(ExportError::AutoParamContract {
                reason: "root autoParam is not one transparent abbrev",
            });
        };
        let [universe] = uparams.as_slice() else {
            return Err(ExportError::AutoParamContract {
                reason: "autoParam does not have one universe parameter",
            });
        };
        let anonymous = NameId(0);
        let Some(lean) = self.lookup_name_str(anonymous, "Lean") else {
            return Err(ExportError::AutoParamContract {
                reason: "Lean namespace is absent",
            });
        };
        let Some(syntax) = self.lookup_name_str(lean, "Syntax") else {
            return Err(ExportError::AutoParamContract {
                reason: "Lean.Syntax is absent",
            });
        };
        let is_universe_sort = |expression| {
            matches!(
                self.expr_node(expression),
                ExprNode::Sort(level)
                    if matches!(self.level_node(*level), LevelNode::Param(name) if name == universe)
            )
        };
        let is_syntax = |expression| {
            matches!(
                self.expr_node(expression),
                ExprNode::Const(name, levels) if *name == syntax && levels.is_empty()
            )
        };
        let ExprNode::Pi(_, alpha_sort, tactic_pi, BinderInfo::Default) = self.expr_node(*ty)
        else {
            return Err(ExportError::AutoParamContract {
                reason: "autoParam type has the wrong outer binder",
            });
        };
        let ExprNode::Pi(_, syntax_ty, result_sort, BinderInfo::Default) =
            self.expr_node(*tactic_pi)
        else {
            return Err(ExportError::AutoParamContract {
                reason: "autoParam type has the wrong tactic binder",
            });
        };
        let ExprNode::Lam(_, value_alpha_sort, value_body, BinderInfo::Default) =
            self.expr_node(*value)
        else {
            return Err(ExportError::AutoParamContract {
                reason: "autoParam value has the wrong outer lambda",
            });
        };
        let ExprNode::Lam(_, value_syntax_ty, value_result, BinderInfo::Default) =
            self.expr_node(*value_body)
        else {
            return Err(ExportError::AutoParamContract {
                reason: "autoParam value has the wrong tactic lambda",
            });
        };
        if !is_universe_sort(*alpha_sort)
            || !is_syntax(*syntax_ty)
            || !is_universe_sort(*result_sort)
            || !is_universe_sort(*value_alpha_sort)
            || !is_syntax(*value_syntax_ty)
            || !matches!(self.expr_node(*value_result), ExprNode::BVar(1))
        {
            return Err(ExportError::AutoParamContract {
                reason: "autoParam type or value is not the canonical identity gadget",
            });
        }
        Ok(())
    }

    fn normalize_auto_param_type(
        &mut self,
        expression: ExprId,
        auto_param: NameId,
        memo: &mut BTreeMap<ExprId, ExprId>,
        rewritten: &mut BTreeSet<ExprId>,
    ) -> ExprId {
        if let Some(&normalized) = memo.get(&expression) {
            return normalized;
        }
        if let Some(ty) = self.auto_param_type_argument(expression, auto_param) {
            let normalized = self.normalize_auto_param_type(ty, auto_param, memo, rewritten);
            rewritten.insert(expression);
            memo.insert(expression, normalized);
            return normalized;
        }
        let node = self.expr_node(expression).clone();
        let normalized = match node {
            ExprNode::Proj(name, field, structure) => {
                let structure =
                    self.normalize_auto_param_type(structure, auto_param, memo, rewritten);
                self.proj(name, field, structure)
            }
            ExprNode::App(function, argument) => {
                let function =
                    self.normalize_auto_param_type(function, auto_param, memo, rewritten);
                let argument =
                    self.normalize_auto_param_type(argument, auto_param, memo, rewritten);
                self.app(function, argument)
            }
            ExprNode::Lam(name, ty, body, info) => {
                let ty = self.normalize_auto_param_type(ty, auto_param, memo, rewritten);
                let body = self.normalize_auto_param_type(body, auto_param, memo, rewritten);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let ty = self.normalize_auto_param_type(ty, auto_param, memo, rewritten);
                let body = self.normalize_auto_param_type(body, auto_param, memo, rewritten);
                self.pi(name, ty, body, info)
            }
            ExprNode::Let(name, ty, value, body) => {
                let ty = self.normalize_auto_param_type(ty, auto_param, memo, rewritten);
                let value = self.normalize_auto_param_type(value, auto_param, memo, rewritten);
                let body = self.normalize_auto_param_type(body, auto_param, memo, rewritten);
                self.let_(name, ty, value, body)
            }
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Const(..)
            | ExprNode::Lit(_) => expression,
        };
        memo.insert(expression, normalized);
        normalized
    }

    fn normalize_auto_param_binder_annotations(
        &mut self,
        expression: ExprId,
        auto_param: NameId,
        memo: &mut BTreeMap<ExprId, ExprId>,
        rewritten: &mut BTreeSet<ExprId>,
    ) -> ExprId {
        if let Some(&normalized) = memo.get(&expression) {
            return normalized;
        }
        let node = self.expr_node(expression).clone();
        let normalized = match node {
            ExprNode::Lam(name, ty, body, info) => {
                let mut type_memo = BTreeMap::new();
                let ty = self.normalize_auto_param_type(ty, auto_param, &mut type_memo, rewritten);
                let body =
                    self.normalize_auto_param_binder_annotations(body, auto_param, memo, rewritten);
                self.lam(name, ty, body, info)
            }
            ExprNode::Pi(name, ty, body, info) => {
                let mut type_memo = BTreeMap::new();
                let ty = self.normalize_auto_param_type(ty, auto_param, &mut type_memo, rewritten);
                let body =
                    self.normalize_auto_param_binder_annotations(body, auto_param, memo, rewritten);
                self.pi(name, ty, body, info)
            }
            ExprNode::Proj(name, field, structure) => {
                let structure = self.normalize_auto_param_binder_annotations(
                    structure, auto_param, memo, rewritten,
                );
                self.proj(name, field, structure)
            }
            ExprNode::App(function, argument) => {
                let function = self
                    .normalize_auto_param_binder_annotations(function, auto_param, memo, rewritten);
                let argument = self
                    .normalize_auto_param_binder_annotations(argument, auto_param, memo, rewritten);
                self.app(function, argument)
            }
            ExprNode::Let(name, ty, value, body) => {
                let value = self
                    .normalize_auto_param_binder_annotations(value, auto_param, memo, rewritten);
                let body =
                    self.normalize_auto_param_binder_annotations(body, auto_param, memo, rewritten);
                self.let_(name, ty, value, body)
            }
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Const(..)
            | ExprNode::Lit(_) => expression,
        };
        memo.insert(expression, normalized);
        normalized
    }

    /// Stream the complete checked environment as official `lean4export`
    /// NDJSON 3.1.0 without accumulating it beside the checked arenas.
    ///
    /// Output is byte-for-byte identical to
    /// [`Self::render_lean4export_ndjson`].
    ///
    /// # Errors
    ///
    /// Returns [`ExportError`] for a write failure or any construct the format
    /// cannot carry.
    pub fn write_lean4export_ndjson<W: io::Write + ?Sized>(
        &self,
        writer: &mut W,
        metadata: &Lean4ExportMetadata,
    ) -> Result<(), ExportError> {
        let normalization = TransportNormalization::default();
        let order = self.order_units(self.export_units()?, &normalization)?;
        self.write_ordered_units(writer, metadata, &order, &normalization)
    }

    /// Stream only the checked declaration closure of `roots` in official
    /// `lean4export` NDJSON 3.1.0 form.
    ///
    /// Output is byte-for-byte identical to
    /// [`Self::render_lean4export_ndjson_roots`].
    ///
    /// # Errors
    ///
    /// Returns a typed [`ExportError`] for an invalid root set, write failure,
    /// or unsupported construct in the selected closure.
    pub fn write_lean4export_ndjson_roots<W: io::Write + ?Sized>(
        &self,
        writer: &mut W,
        metadata: &Lean4ExportMetadata,
        roots: &[NameId],
    ) -> Result<(), ExportError> {
        let normalization = TransportNormalization::default();
        let units = self.select_root_units(self.export_units()?, roots, &normalization)?;
        let order = self.order_units(units, &normalization)?;
        self.write_ordered_units(writer, metadata, &order, &normalization)
    }

    fn write_ordered_units<W: io::Write + ?Sized>(
        &self,
        writer: &mut W,
        metadata: &Lean4ExportMetadata,
        order: &[Unit],
        normalization: &TransportNormalization,
    ) -> Result<(), ExportError> {
        let mut emitter = Emitter {
            kernel: self,
            writer,
            names: BTreeMap::new(),
            levels: BTreeMap::new(),
            expressions: BTreeMap::new(),
            next_name: 1,
            next_level: 1,
            next_expression: 0,
            normalization,
        };
        emitter.metadata(metadata)?;
        for unit in order {
            emitter.unit(unit)?;
        }
        Ok(())
    }

    /// Retain exactly the atomic units reachable from `roots`.
    fn select_root_units(
        &self,
        units: Vec<Unit>,
        roots: &[NameId],
        normalization: &TransportNormalization,
    ) -> Result<Vec<Unit>, ExportError> {
        self.select_root_units_with_theorem_leaves(units, roots, normalization, &BTreeSet::new())
    }

    fn select_root_units_with_theorem_leaves(
        &self,
        units: Vec<Unit>,
        roots: &[NameId],
        normalization: &TransportNormalization,
        theorem_leaves: &BTreeSet<NameId>,
    ) -> Result<Vec<Unit>, ExportError> {
        if roots.is_empty() {
            return Err(ExportError::EmptyRoots);
        }
        let mut owner: BTreeMap<NameId, usize> = BTreeMap::new();
        for (index, unit) in units.iter().enumerate() {
            for member in unit.members() {
                owner.insert(member, index);
            }
        }
        let mut selected = BTreeSet::new();
        let mut work = Vec::new();
        for &root in roots {
            let Some(&index) = owner.get(&root) else {
                return Err(ExportError::MissingRoot {
                    name: self.display_name(root).to_string(),
                });
            };
            if selected.insert(index) {
                work.push(index);
            }
        }
        while let Some(index) = work.pop() {
            for member in units[index].members() {
                for dependency in
                    self.member_constants_with_theorem_leaves(member, normalization, theorem_leaves)
                {
                    if let Some(&dependency_index) = owner.get(&dependency)
                        && selected.insert(dependency_index)
                    {
                        work.push(dependency_index);
                    }
                }
            }
        }
        Ok(units
            .into_iter()
            .enumerate()
            .filter_map(|(index, unit)| selected.contains(&index).then_some(unit))
            .collect())
    }

    /// Partition the environment into atomic emission units, failing closed on
    /// any declaration that no unit claims.
    #[allow(clippy::too_many_lines)]
    fn export_units(&self) -> Result<Vec<Unit>, ExportError> {
        let mut units: Vec<Unit> = Vec::new();
        let mut quotient: Vec<NameId> = Vec::new();
        let mut claimed: BTreeSet<NameId> = BTreeSet::new();

        // Recursor names are `I.rec` for each family and `I₀.rec_<n>` for the
        // auxiliary recursors of a nested group, so they can be attributed to a
        // family by name structure alone (the kernel does not store a parent on
        // `Declaration::Recursor`). Attribution is by lookup, never by interning
        // a fresh name, so this stays a `&self` traversal.
        let mut main_recursors: BTreeMap<NameId, NameId> = BTreeMap::new();
        let mut auxiliary_recursors: BTreeMap<NameId, BTreeMap<u64, NameId>> = BTreeMap::new();
        for (&name, declaration) in self.environment().iter() {
            if !matches!(declaration, Declaration::Recursor { .. }) {
                continue;
            }
            let NameNode::Str(parent, component) = self.name_node(name) else {
                return Err(ExportError::UnclaimedRecursor {
                    name: self.display_name(name).to_string(),
                });
            };
            if component == "rec" {
                main_recursors.insert(*parent, name);
            } else if let Some(suffix) = component.strip_prefix("rec_") {
                let Ok(suffix) = suffix.parse::<u64>() else {
                    return Err(ExportError::UnclaimedRecursor {
                        name: self.display_name(name).to_string(),
                    });
                };
                auxiliary_recursors
                    .entry(*parent)
                    .or_default()
                    .insert(suffix, name);
            } else {
                return Err(ExportError::UnclaimedRecursor {
                    name: self.display_name(name).to_string(),
                });
            }
        }

        for (&name, declaration) in self.environment().iter() {
            match declaration {
                Declaration::Inductive { .. } => {
                    let families = self
                        .environment()
                        .inductive_group(name)
                        .map_or_else(|| vec![name], <[NameId]>::to_vec);
                    if families[0] != name {
                        continue;
                    }
                    let mut constructors = Vec::new();
                    let mut recursors = Vec::new();
                    for &family in &families {
                        let Some(Declaration::Inductive { ctor_names, .. }) =
                            self.environment().get(family)
                        else {
                            return Err(ExportError::MissingGroupDeclaration {
                                name: self.display_name(family).to_string(),
                            });
                        };
                        constructors.extend(ctor_names.iter().copied());
                        let Some(&recursor) = main_recursors.get(&family) else {
                            return Err(ExportError::MissingGroupDeclaration {
                                name: format!("{}.rec", self.display_name(family)),
                            });
                        };
                        recursors.push(recursor);
                    }
                    if let Some(auxiliary) = auxiliary_recursors.get(&families[0]) {
                        recursors.extend(auxiliary.values().copied());
                    }
                    for &member in families
                        .iter()
                        .chain(&constructors)
                        .chain(&recursors)
                        .collect::<Vec<_>>()
                    {
                        claimed.insert(member);
                    }
                    units.push(Unit::Inductive(InductiveUnit {
                        families,
                        constructors,
                        recursors,
                    }));
                }
                Declaration::Quotient { .. } => quotient.push(name),
                Declaration::Constructor { .. } | Declaration::Recursor { .. } => {}
                Declaration::Axiom { .. }
                | Declaration::Definition { .. }
                | Declaration::Theorem { .. }
                | Declaration::Opaque { .. } => {
                    claimed.insert(name);
                    units.push(Unit::Single(name));
                }
            }
        }

        if !quotient.is_empty() {
            if quotient.len() != 4 {
                return Err(ExportError::IncompleteQuotientPackage {
                    present: quotient.len(),
                });
            }
            let mut ordered = Vec::with_capacity(4);
            for kind in [
                QuotKind::Type,
                QuotKind::Ctor,
                QuotKind::Lift,
                QuotKind::Ind,
            ] {
                let member = quotient.iter().copied().find(|&name| {
                    matches!(self.environment().get(name), Some(Declaration::Quotient { kind: stored, .. }) if *stored == kind)
                });
                let Some(member) = member else {
                    return Err(ExportError::IncompleteQuotientPackage {
                        present: quotient.len(),
                    });
                };
                claimed.insert(member);
                ordered.push(member);
            }
            units.push(Unit::Quotient(ordered));
        }

        // Nothing may be dropped: every declaration in the environment must be
        // claimed by exactly one unit.
        for (&name, declaration) in self.environment().iter() {
            if claimed.contains(&name) {
                continue;
            }
            return Err(match declaration {
                Declaration::Constructor { .. } => ExportError::UnclaimedConstructor {
                    name: self.display_name(name).to_string(),
                },
                _ => ExportError::UnclaimedRecursor {
                    name: self.display_name(name).to_string(),
                },
            });
        }
        Ok(units)
    }

    /// Deterministically order units so every referenced constant is declared
    /// before it is used. Unit keys are `NameId`s and the traversal is
    /// id-ordered, so the emitted order depends only on the environment.
    fn order_units(
        &self,
        units: Vec<Unit>,
        normalization: &TransportNormalization,
    ) -> Result<Vec<Unit>, ExportError> {
        self.order_units_with_theorem_leaves(units, normalization, &BTreeSet::new())
    }

    fn order_units_with_theorem_leaves(
        &self,
        units: Vec<Unit>,
        normalization: &TransportNormalization,
        theorem_leaves: &BTreeSet<NameId>,
    ) -> Result<Vec<Unit>, ExportError> {
        let mut owner: BTreeMap<NameId, usize> = BTreeMap::new();
        for (index, unit) in units.iter().enumerate() {
            for member in unit.members() {
                owner.insert(member, index);
            }
        }
        let dependencies: Vec<Vec<usize>> = units
            .iter()
            .enumerate()
            .map(|(index, unit)| -> Result<Vec<usize>, ExportError> {
                let mut referenced = BTreeSet::new();
                for member in unit.members() {
                    for constant in self.member_constants_with_theorem_leaves(
                        member,
                        normalization,
                        theorem_leaves,
                    ) {
                        let Some(&other) = owner.get(&constant) else {
                            return Err(ExportError::MissingDependency {
                                declaration: self.display_name(member).to_string(),
                                dependency: self.display_name(constant).to_string(),
                            });
                        };
                        if other != index {
                            referenced.insert(other);
                        }
                    }
                }
                Ok(referenced.into_iter().collect())
            })
            .collect::<Result<_, _>>()?;

        let mut marks = vec![Mark::Unvisited; units.len()];
        let mut order = Vec::with_capacity(units.len());
        let mut roots: Vec<usize> = (0..units.len()).collect();
        roots.sort_by_key(|&index| units[index].key());
        for root in roots {
            if marks[root] != Mark::Unvisited {
                continue;
            }
            let mut stack = vec![(root, 0usize)];
            marks[root] = Mark::OnStack;
            while let Some((index, cursor)) = stack.pop() {
                if let Some(&next) = dependencies[index].get(cursor) {
                    stack.push((index, cursor + 1));
                    match marks[next] {
                        Mark::Done => {}
                        Mark::OnStack => {
                            let mut names: Vec<String> = stack
                                .iter()
                                .map(|&(unit, _)| self.display_name(units[unit].key()).to_string())
                                .collect();
                            names.push(self.display_name(units[next].key()).to_string());
                            return Err(ExportError::DependencyCycle { names });
                        }
                        Mark::Unvisited => {
                            marks[next] = Mark::OnStack;
                            stack.push((next, 0));
                        }
                    }
                } else {
                    marks[index] = Mark::Done;
                    order.push(index);
                }
            }
        }
        let mut ordered: Vec<Option<Unit>> = units.into_iter().map(Some).collect();
        Ok(order
            .into_iter()
            .filter_map(|index| ordered[index].take())
            .collect())
    }

    /// Every constant referenced by one declaration's type, value, and — for a
    /// recursor — its ι-reduction rules.
    fn member_constants(
        &self,
        member: NameId,
        normalization: &TransportNormalization,
    ) -> BTreeSet<NameId> {
        let mut constants = BTreeSet::new();
        let Some(declaration) = self.environment().get(member) else {
            return constants;
        };
        let mut roots = vec![
            normalization
                .types
                .get(&member)
                .map_or_else(|| declaration.ty(), |normalized| normalized.expression),
        ];
        if let Some(value) = declaration.value() {
            roots.push(value);
        }
        if let Declaration::Recursor { rec_rules, .. } = declaration {
            roots.extend(rec_rules.iter().enumerate().map(|(index, rule)| {
                normalization
                    .recursor_rules
                    .get(&(member, index))
                    .map_or(rule.value, |normalized| normalized.expression)
            }));
            constants.extend(rec_rules.iter().map(|rule| rule.ctor_name));
        }
        let mut visited = BTreeSet::new();
        while let Some(expression) = roots.pop() {
            if !visited.insert(expression) {
                continue;
            }
            match self.expr_node(expression) {
                ExprNode::Const(name, _) => {
                    constants.insert(*name);
                }
                ExprNode::Proj(type_name, _, structure) => {
                    constants.insert(*type_name);
                    roots.push(*structure);
                }
                ExprNode::App(function, argument) => {
                    roots.push(*function);
                    roots.push(*argument);
                }
                ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                    roots.push(*ty);
                    roots.push(*body);
                }
                ExprNode::Let(_, ty, value, body) => {
                    roots.push(*ty);
                    roots.push(*value);
                    roots.push(*body);
                }
                ExprNode::Lit(Lit::Str(_)) => {
                    constants.extend(self.string_literal_dependency_names());
                }
                ExprNode::BVar(_)
                | ExprNode::FVar(_)
                | ExprNode::Sort(_)
                | ExprNode::Lit(Lit::Nat(_)) => {}
            }
        }
        constants
    }

    fn member_constants_with_theorem_leaves(
        &self,
        member: NameId,
        normalization: &TransportNormalization,
        theorem_leaves: &BTreeSet<NameId>,
    ) -> BTreeSet<NameId> {
        if !theorem_leaves.contains(&member) {
            return self.member_constants(member, normalization);
        }
        let Some(Declaration::Theorem { ty, .. }) = self.environment().get(member) else {
            return BTreeSet::new();
        };
        let ty = normalization
            .types
            .get(&member)
            .map_or(*ty, |normalized| normalized.expression);
        self.expression_constants(vec![ty])
    }

    fn expression_constants(&self, mut roots: Vec<ExprId>) -> BTreeSet<NameId> {
        let mut constants = BTreeSet::new();
        let mut visited = BTreeSet::new();
        while let Some(expression) = roots.pop() {
            if !visited.insert(expression) {
                continue;
            }
            match self.expr_node(expression) {
                ExprNode::Const(name, _) => {
                    constants.insert(*name);
                }
                ExprNode::Proj(type_name, _, structure) => {
                    constants.insert(*type_name);
                    roots.push(*structure);
                }
                ExprNode::App(function, argument) => {
                    roots.push(*function);
                    roots.push(*argument);
                }
                ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                    roots.push(*ty);
                    roots.push(*body);
                }
                ExprNode::Let(_, ty, value, body) => {
                    roots.push(*ty);
                    roots.push(*value);
                    roots.push(*body);
                }
                ExprNode::Lit(Lit::Str(_)) => {
                    constants.extend(self.string_literal_dependency_names());
                }
                ExprNode::BVar(_)
                | ExprNode::FVar(_)
                | ExprNode::Sort(_)
                | ExprNode::Lit(Lit::Nat(_)) => {}
            }
        }
        constants
    }

    /// Reserved declarations whose checked shapes give string literals their
    /// type and constructor expansion. Literals carry no explicit `Const`
    /// edges, so root selection must add these semantic dependencies itself.
    pub(crate) fn string_literal_dependency_names(&self) -> Vec<NameId> {
        let anonymous = NameId(0);
        let Some(string) = self.lookup_name_str(anonymous, "String") else {
            return Vec::new();
        };
        let Some(char_) = self.lookup_name_str(anonymous, "Char") else {
            return Vec::new();
        };
        let Some(list) = self.lookup_name_str(anonymous, "List") else {
            return Vec::new();
        };
        let Some(nat) = self.lookup_name_str(anonymous, "Nat") else {
            return Vec::new();
        };
        let Some(of_list) = self.lookup_name_str(string, "ofList") else {
            return Vec::new();
        };
        let Some(char_of_nat) = self.lookup_name_str(char_, "ofNat") else {
            return Vec::new();
        };
        vec![string, char_, list, nat, of_list, char_of_nat]
    }

    /// Lean's reflexivity predicate, which the wire format records as the
    /// family's `isReflexive` flag: some constructor takes a **function**
    /// argument whose result type is a member of the group. `Acc.intro`'s
    /// accessibility hypothesis is the canonical case. The kernel does not
    /// store the flag, so it is derived; the round-trip suite checks the
    /// derivation against every official v4.30 fixture.
    fn is_reflexive_inductive(&self, family: NameId, group: &[NameId]) -> bool {
        let Some(Declaration::Inductive {
            num_params,
            ctor_names,
            ..
        }) = self.environment().get(family)
        else {
            return false;
        };
        let num_params = usize::from(*num_params);
        ctor_names.iter().any(|&constructor| {
            let Some(Declaration::Constructor { ty, .. }) = self.environment().get(constructor)
            else {
                return false;
            };
            let mut field = *ty;
            for _ in 0..num_params {
                match self.expr_node(field) {
                    ExprNode::Pi(_, _, body, _) => field = *body,
                    _ => return false,
                }
            }
            while let ExprNode::Pi(_, field_ty, body, _) = self.expr_node(field) {
                if self.is_reflexive_field(*field_ty, group) {
                    return true;
                }
                field = *body;
            }
            false
        })
    }

    /// A constructor field is reflexive when it is a function type whose result
    /// head is one of the group's families.
    fn is_reflexive_field(&self, field: ExprId, group: &[NameId]) -> bool {
        let mut result = field;
        let mut is_function = false;
        while let ExprNode::Pi(_, _, body, _) = self.expr_node(result) {
            is_function = true;
            result = *body;
        }
        if !is_function {
            return false;
        }
        let mut head = result;
        while let ExprNode::App(function, _) = self.expr_node(head) {
            head = *function;
        }
        matches!(self.expr_node(head), ExprNode::Const(name, _) if group.contains(name))
    }

    /// Lean 4.30's K-like predicate, which the wire format records as the
    /// recursor's `k` flag: a `Prop`-valued family with exactly one constructor
    /// whose only arguments are the family's parameters. The kernel does not
    /// store the flag, so it is derived; the round-trip suite checks the
    /// derivation against every official v4.30 fixture.
    ///
    /// Public because an *importer* has to check the flag too, and there is
    /// exactly one right answer to check against. Believing a family is K-like
    /// licenses reducing a recursor application whose major premise is not a
    /// constructor, so an import that accepted the wire's `k` on trust would be
    /// taking a soundness-critical decision from the stream. Reading it here
    /// instead of reimplementing the predicate is the point of exposing it.
    #[must_use]
    pub fn is_k_like_inductive(&self, family: NameId) -> bool {
        let Some(Declaration::Inductive { ty, ctor_names, .. }) = self.environment().get(family)
        else {
            return false;
        };
        if ctor_names.len() != 1 {
            return false;
        }
        if self
            .environment()
            .inductive_group(family)
            .is_some_and(|group| group.len() > 1)
        {
            return false;
        }
        let mut result = *ty;
        while let ExprNode::Pi(_, _, body, _) = self.expr_node(result) {
            result = *body;
        }
        let ExprNode::Sort(level) = self.expr_node(result) else {
            return false;
        };
        if !matches!(self.level_node(*level), LevelNode::Zero) {
            return false;
        }
        let Some(Declaration::Constructor { num_fields, .. }) =
            self.environment().get(ctor_names[0])
        else {
            return false;
        };
        *num_fields == 0
    }
}

/// The NDJSON writer's mutable index state.
///
/// Index 0 of the name space is the anonymous name and index 0 of the level
/// space is `Level.zero`; the format leaves both implicit, so neither is ever
/// emitted as a record.
struct Emitter<'kernel, W: io::Write + ?Sized> {
    kernel: &'kernel Kernel,
    writer: &'kernel mut W,
    normalization: &'kernel TransportNormalization,
    names: BTreeMap<NameId, usize>,
    levels: BTreeMap<LevelId, usize>,
    expressions: BTreeMap<ExprId, usize>,
    next_name: usize,
    next_level: usize,
    next_expression: usize,
}

impl<W: io::Write + ?Sized> Emitter<'_, W> {
    fn line(&mut self, record: &str) -> Result<(), ExportError> {
        self.writer.write_all(record.as_bytes())?;
        self.writer.write_all(b"\n")?;
        Ok(())
    }

    fn metadata(&mut self, metadata: &Lean4ExportMetadata) -> Result<(), ExportError> {
        let record = format!(
            "{{\"meta\":{{\"exporter\":{{\"name\":\"lean4export\",\"version\":{}}},\"format\":{{\"version\":{}}},\"lean\":{{\"githash\":{},\"version\":{}}}}}}}",
            json_string(&metadata.exporter_version),
            json_string(EXPORT_FORMAT_VERSION),
            json_string(&metadata.lean_githash),
            json_string(&metadata.lean_version),
        );
        self.line(&record)
    }

    /// The wire index of `name`, emitting its ancestors first. The anonymous
    /// name is index 0 and is never emitted.
    fn name(&mut self, name: NameId) -> Result<usize, ExportError> {
        if let Some(&index) = self.names.get(&name) {
            return Ok(index);
        }
        if matches!(self.kernel.name_node(name), NameNode::Anonymous) {
            self.names.insert(name, 0);
            return Ok(0);
        }
        // Hierarchical names are short, but the parent chain is walked
        // iteratively so a pathological name cannot overflow the stack.
        let mut chain = Vec::new();
        let mut cursor = name;
        loop {
            if self.names.contains_key(&cursor) {
                break;
            }
            match self.kernel.name_node(cursor) {
                NameNode::Anonymous => {
                    self.names.insert(cursor, 0);
                    break;
                }
                NameNode::Str(parent, _) | NameNode::Num(parent, _) => {
                    chain.push(cursor);
                    cursor = *parent;
                }
            }
        }
        for &current in chain.iter().rev() {
            let index = self.next_name;
            let record = match self.kernel.name_node(current) {
                NameNode::Str(parent, component) => {
                    let parent = self.names[parent];
                    format!(
                        "{{\"in\":{index},\"str\":{{\"pre\":{parent},\"str\":{}}}}}",
                        json_string(component)
                    )
                }
                NameNode::Num(parent, component) => {
                    let parent = self.names[parent];
                    format!("{{\"in\":{index},\"num\":{{\"pre\":{parent},\"i\":{component}}}}}")
                }
                NameNode::Anonymous => unreachable!("the anonymous name is pre-assigned index 0"),
            };
            self.line(&record)?;
            self.names.insert(current, index);
            self.next_name += 1;
        }
        Ok(self.names[&name])
    }

    /// The wire index of `level`. `Level.zero` is index 0 and is never emitted.
    fn level(&mut self, level: LevelId) -> Result<usize, ExportError> {
        if let Some(&index) = self.levels.get(&level) {
            return Ok(index);
        }
        let record = match self.kernel.level_node(level) {
            LevelNode::Zero => {
                self.levels.insert(level, 0);
                return Ok(0);
            }
            LevelNode::Succ(prior) => {
                let prior = self.level(*prior)?;
                format!("{{\"il\":{},\"succ\":{prior}}}", self.next_level)
            }
            LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                let kind = if matches!(self.kernel.level_node(level), LevelNode::Max(_, _)) {
                    "max"
                } else {
                    "imax"
                };
                let left = self.level(*left)?;
                let right = self.level(*right)?;
                format!("{{\"il\":{},\"{kind}\":[{left},{right}]}}", self.next_level)
            }
            LevelNode::Param(name) => {
                let name = self.name(*name)?;
                format!("{{\"il\":{},\"param\":{name}}}", self.next_level)
            }
        };
        let index = self.next_level;
        self.line(&record)?;
        self.levels.insert(level, index);
        self.next_level += 1;
        Ok(index)
    }

    fn level_list(&mut self, levels: &[LevelId]) -> Result<String, ExportError> {
        let mut indices = Vec::with_capacity(levels.len());
        for &level in levels {
            indices.push(self.level(level)?.to_string());
        }
        Ok(format!("[{}]", indices.join(",")))
    }

    fn name_list(&mut self, names: &[NameId]) -> Result<String, ExportError> {
        let mut indices = Vec::with_capacity(names.len());
        for &name in names {
            indices.push(self.name(name)?.to_string());
        }
        Ok(format!("[{}]", indices.join(",")))
    }

    /// The wire index of `expression`, emitting every subterm first.
    ///
    /// The traversal is an explicit post-order so a corpus-scale proof term
    /// cannot overflow the stack.
    fn expression(&mut self, expression: ExprId, label: &str) -> Result<usize, ExportError> {
        if let Some(&index) = self.expressions.get(&expression) {
            return Ok(index);
        }
        let mut postorder = Vec::new();
        let mut visited = BTreeSet::new();
        let mut stack = vec![(expression, false)];
        while let Some((current, expanded)) = stack.pop() {
            if expanded {
                postorder.push(current);
                continue;
            }
            if self.expressions.contains_key(&current) || !visited.insert(current) {
                continue;
            }
            stack.push((current, true));
            match self.kernel.expr_node(current) {
                ExprNode::Proj(_, _, structure) => stack.push((*structure, false)),
                ExprNode::App(function, argument) => {
                    stack.push((*function, false));
                    stack.push((*argument, false));
                }
                ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                    stack.push((*ty, false));
                    stack.push((*body, false));
                }
                ExprNode::Let(_, ty, value, body) => {
                    stack.push((*ty, false));
                    stack.push((*value, false));
                    stack.push((*body, false));
                }
                ExprNode::BVar(_)
                | ExprNode::FVar(_)
                | ExprNode::Sort(_)
                | ExprNode::Const(..)
                | ExprNode::Lit(_) => {}
            }
        }
        for current in postorder {
            if self.expressions.contains_key(&current) {
                continue;
            }
            self.expression_record(current, label)?;
        }
        Ok(self.expressions[&expression])
    }

    fn expression_record(&mut self, expression: ExprId, label: &str) -> Result<(), ExportError> {
        let index = self.next_expression;
        let body = match self.kernel.expr_node(expression).clone() {
            ExprNode::BVar(de_bruijn) => format!("\"bvar\":{de_bruijn}"),
            ExprNode::FVar(_) => {
                return Err(ExportError::FreeVariable {
                    declaration: label.to_owned(),
                });
            }
            ExprNode::Sort(level) => {
                let level = self.level(level)?;
                format!("\"sort\":{level}")
            }
            ExprNode::Const(name, levels) => {
                let name = self.name(name)?;
                let levels = self.level_list(&levels)?;
                format!("\"const\":{{\"name\":{name},\"us\":{levels}}}")
            }
            ExprNode::App(function, argument) => {
                let function = self.expressions[&function];
                let argument = self.expressions[&argument];
                format!("\"app\":{{\"arg\":{argument},\"fn\":{function}}}")
            }
            ExprNode::Lam(name, ty, body, info) | ExprNode::Pi(name, ty, body, info) => {
                let kind = if matches!(self.kernel.expr_node(expression), ExprNode::Lam(..)) {
                    "lam"
                } else {
                    "forallE"
                };
                let name = self.name(name)?;
                let ty = self.expressions[&ty];
                let body = self.expressions[&body];
                format!(
                    "\"{kind}\":{{\"binderInfo\":\"{}\",\"body\":{body},\"name\":{name},\"type\":{ty}}}",
                    binder_info_name(info)
                )
            }
            ExprNode::Let(name, ty, value, body) => {
                let name = self.name(name)?;
                let ty = self.expressions[&ty];
                let value = self.expressions[&value];
                let body = self.expressions[&body];
                // The kernel does not model Lean 4.30's `nondep` let marker; the
                // conservative (dependent) form is emitted, and the importer
                // treats the field as descriptive.
                format!(
                    "\"letE\":{{\"body\":{body},\"name\":{name},\"nondep\":false,\"type\":{ty},\"value\":{value}}}"
                )
            }
            ExprNode::Proj(type_name, field, structure) => {
                let structure = self.expressions[&structure];
                let type_name = self.name(type_name)?;
                format!(
                    "\"proj\":{{\"idx\":{field},\"struct\":{structure},\"typeName\":{type_name}}}"
                )
            }
            ExprNode::Lit(Lit::Nat(value)) => format!("\"natVal\":\"{value}\""),
            ExprNode::Lit(Lit::Str(value)) => {
                format!("\"strVal\":{}", json_string(&value))
            }
        };
        // Lean's `Json` writer emits object fields in alphabetical order, so
        // `{"app":…,"ie":n}` but `{"ie":n,"sort":…}`. Matching it costs nothing
        // and keeps our records diffable against an official export.
        let kind_key = body
            .split_once('"')
            .and_then(|(_, rest)| rest.split_once('"'))
            .map_or("", |(kind, _)| kind);
        if kind_key < "ie" {
            self.line(&format!("{{{body},\"ie\":{index}}}"))?;
        } else {
            self.line(&format!("{{\"ie\":{index},{body}}}"))?;
        }
        self.expressions.insert(expression, index);
        self.next_expression += 1;
        Ok(())
    }

    fn unit(&mut self, unit: &Unit) -> Result<(), ExportError> {
        match unit {
            Unit::Single(name) => self.single(*name),
            Unit::Inductive(inductive) => self.inductive(inductive),
            Unit::Quotient(members) => {
                for &member in members {
                    self.quotient(member)?;
                }
                Ok(())
            }
        }
    }

    fn single(&mut self, name: NameId) -> Result<(), ExportError> {
        let Some(declaration) = self.kernel.environment().get(name).cloned() else {
            return Err(ExportError::MissingGroupDeclaration {
                name: self.kernel.display_name(name).to_string(),
            });
        };
        let label = self.kernel.display_name(name).to_string();
        let uparams = self.name_list(declaration.uparams())?;
        let ty = self.expression(
            self.normalization
                .types
                .get(&name)
                .map_or_else(|| declaration.ty(), |normalized| normalized.expression),
            &label,
        )?;
        let index = self.name(name)?;
        let all = format!("[{index}]");
        let record = match &declaration {
            Declaration::Axiom { .. } => format!(
                "{{\"axiom\":{{\"isUnsafe\":false,\"levelParams\":{uparams},\"name\":{index},\"type\":{ty}}}}}"
            ),
            Declaration::Definition { value, hint, .. } => {
                let value = self.expression(*value, &label)?;
                let hints = match hint {
                    ReducibilityHint::Opaque => "\"opaque\"".to_owned(),
                    ReducibilityHint::Abbrev => "\"abbrev\"".to_owned(),
                    ReducibilityHint::Regular(height) => format!("{{\"regular\":{height}}}"),
                };
                format!(
                    "{{\"def\":{{\"all\":{all},\"hints\":{hints},\"levelParams\":{uparams},\"name\":{index},\"safety\":\"safe\",\"type\":{ty},\"value\":{value}}}}}"
                )
            }
            Declaration::Theorem { value, .. } => {
                let value = self.expression(*value, &label)?;
                format!(
                    "{{\"thm\":{{\"all\":{all},\"levelParams\":{uparams},\"name\":{index},\"type\":{ty},\"value\":{value}}}}}"
                )
            }
            Declaration::Opaque { value, .. } => {
                let value = self.expression(*value, &label)?;
                format!(
                    "{{\"opaque\":{{\"all\":{all},\"isUnsafe\":false,\"levelParams\":{uparams},\"name\":{index},\"type\":{ty},\"value\":{value}}}}}"
                )
            }
            Declaration::Inductive { .. }
            | Declaration::Constructor { .. }
            | Declaration::Recursor { .. }
            | Declaration::Quotient { .. } => {
                return Err(ExportError::MissingGroupDeclaration { name: label });
            }
        };
        self.line(&record)
    }

    fn quotient(&mut self, name: NameId) -> Result<(), ExportError> {
        let Some(Declaration::Quotient {
            uparams, ty, kind, ..
        }) = self.kernel.environment().get(name).cloned()
        else {
            return Err(ExportError::IncompleteQuotientPackage { present: 0 });
        };
        let label = self.kernel.display_name(name).to_string();
        let uparams = self.name_list(&uparams)?;
        let ty = self.expression(ty, &label)?;
        let index = self.name(name)?;
        let kind = match kind {
            QuotKind::Type => "type",
            QuotKind::Ctor => "ctor",
            QuotKind::Lift => "lift",
            QuotKind::Ind => "ind",
        };
        self.line(&format!(
            "{{\"quot\":{{\"kind\":\"{kind}\",\"levelParams\":{uparams},\"name\":{index},\"type\":{ty}}}}}"
        ))
    }

    #[allow(clippy::too_many_lines)]
    fn inductive(&mut self, unit: &InductiveUnit) -> Result<(), ExportError> {
        let all = self.name_list(&unit.families)?;
        let mut types = Vec::with_capacity(unit.families.len());
        let mut nested = 0usize;
        if let Some(&first) = unit.recursors.first()
            && let Some(Declaration::Recursor { num_motives, .. }) =
                self.kernel.environment().get(first)
        {
            nested = usize::from(*num_motives).saturating_sub(unit.families.len());
        }
        for &family in &unit.families {
            let Some(Declaration::Inductive {
                uparams,
                ty,
                num_params,
                num_indices,
                is_recursive,
                ctor_names,
                ..
            }) = self.kernel.environment().get(family).cloned()
            else {
                return Err(ExportError::MissingGroupDeclaration {
                    name: self.kernel.display_name(family).to_string(),
                });
            };
            let label = self.kernel.display_name(family).to_string();
            let uparams = self.name_list(&uparams)?;
            let ty = self.expression(
                self.normalization
                    .types
                    .get(&family)
                    .map_or(ty, |normalized| normalized.expression),
                &label,
            )?;
            let constructors = self.name_list(&ctor_names)?;
            let index = self.name(family)?;
            let is_reflexive = self.kernel.is_reflexive_inductive(family, &unit.families);
            types.push(format!(
                "{{\"all\":{all},\"ctors\":{constructors},\"isRec\":{is_recursive},\"isReflexive\":{is_reflexive},\"isUnsafe\":false,\"levelParams\":{uparams},\"name\":{index},\"numIndices\":{num_indices},\"numNested\":{nested},\"numParams\":{num_params},\"type\":{ty}}}"
            ));
        }

        let mut constructors = Vec::with_capacity(unit.constructors.len());
        for &constructor in &unit.constructors {
            let Some(Declaration::Constructor {
                uparams,
                ty,
                inductive,
                idx,
                num_fields,
                ..
            }) = self.kernel.environment().get(constructor).cloned()
            else {
                return Err(ExportError::MissingGroupDeclaration {
                    name: self.kernel.display_name(constructor).to_string(),
                });
            };
            let label = self.kernel.display_name(constructor).to_string();
            let Some(Declaration::Inductive { num_params, .. }) =
                self.kernel.environment().get(inductive)
            else {
                return Err(ExportError::UnclaimedConstructor { name: label });
            };
            let num_params = *num_params;
            let uparams = self.name_list(&uparams)?;
            let ty = self.expression(
                self.normalization
                    .types
                    .get(&constructor)
                    .map_or(ty, |normalized| normalized.expression),
                &label,
            )?;
            let parent = self.name(inductive)?;
            let index = self.name(constructor)?;
            constructors.push(format!(
                "{{\"cidx\":{idx},\"induct\":{parent},\"isUnsafe\":false,\"levelParams\":{uparams},\"name\":{index},\"numFields\":{num_fields},\"numParams\":{num_params},\"type\":{ty}}}"
            ));
        }

        let mut recursors = Vec::with_capacity(unit.recursors.len());
        for (position, &recursor) in unit.recursors.iter().enumerate() {
            let Some(Declaration::Recursor {
                uparams,
                ty,
                rec_rules,
                num_motives,
                num_minors,
                num_params,
                num_indices,
                ..
            }) = self.kernel.environment().get(recursor).cloned()
            else {
                return Err(ExportError::MissingGroupDeclaration {
                    name: self.kernel.display_name(recursor).to_string(),
                });
            };
            let label = self.kernel.display_name(recursor).to_string();
            // K applies only to a source family's own recursor, never to a
            // nested auxiliary one.
            let k_like = unit
                .families
                .get(position)
                .is_some_and(|&family| nested == 0 && self.kernel.is_k_like_inductive(family));
            let mut rules = Vec::with_capacity(rec_rules.len());
            for (rule_index, rule) in rec_rules.iter().enumerate() {
                let rhs = self.expression(
                    self.normalization
                        .recursor_rules
                        .get(&(recursor, rule_index))
                        .map_or(rule.value, |normalized| normalized.expression),
                    &label,
                )?;
                let constructor = self.name(rule.ctor_name)?;
                rules.push(format!(
                    "{{\"ctor\":{constructor},\"nfields\":{},\"rhs\":{rhs}}}",
                    rule.num_fields
                ));
            }
            let uparams = self.name_list(&uparams)?;
            let ty = self.expression(
                self.normalization
                    .types
                    .get(&recursor)
                    .map_or(ty, |normalized| normalized.expression),
                &label,
            )?;
            let index = self.name(recursor)?;
            recursors.push(format!(
                "{{\"all\":{all},\"isUnsafe\":false,\"k\":{k_like},\"levelParams\":{uparams},\"name\":{index},\"numIndices\":{num_indices},\"numMinors\":{num_minors},\"numMotives\":{num_motives},\"numParams\":{num_params},\"rules\":[{}],\"type\":{ty}}}",
                rules.join(",")
            ));
        }

        self.line(&format!(
            "{{\"inductive\":{{\"ctors\":[{}],\"recs\":[{}],\"types\":[{}]}}}}",
            constructors.join(","),
            recursors.join(","),
            types.join(",")
        ))
    }
}

const fn binder_info_name(info: BinderInfo) -> &'static str {
    match info {
        BinderInfo::Default => "default",
        BinderInfo::Implicit => "implicit",
        BinderInfo::StrictImplicit => "strictImplicit",
        BinderInfo::InstImplicit => "instImplicit",
    }
}

/// A JSON string literal. Control characters are escaped; other code points are
/// transmitted raw, which is valid JSON and matches Lean's own writer.
fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for character in value.chars() {
        // Lean's `Lean.Json.escapeAux`, verbatim: only `"`, `\`, `\n` and `\r`
        // get a short escape; every other character below `0x20` — tab and
        // backspace and form feed included — is written `\u00xx` with lowercase
        // hex digits (`Nat.digitChar`), and everything at or above `0x20` is
        // emitted raw. Writing `\t` here instead would produce a stream that
        // parses identically and is NOT byte-identical to lean4export's, which
        // is the only thing the round-trip gate can check.
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            control if control < ' ' => {
                let _ = write!(out, "\\u{:04x}", u32::from(control));
            }
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{ExportError, Lean4ExportMetadata};
    use crate::{
        BinderInfo, Declaration, ExprId, ExprNode, Kernel, Lit, NameId, QuotKind, ReducibilityHint,
        build_logic_prelude,
    };

    /// The environment states below cannot be reached through the trusted
    /// admission gates — a free variable, a string literal, a stray recursor and
    /// a half quotient package are all rejected before insertion. They are
    /// planted with the untrusted insert precisely so the *writer's* fail-closed
    /// behaviour is measured rather than assumed: an emitter that silently drops
    /// what it cannot express would produce a stream a consumer checks less of
    /// than the kernel did.
    fn kernel_with_logic() -> Kernel {
        let mut kernel = Kernel::new();
        build_logic_prelude(&mut kernel).expect("logic prelude must build");
        kernel
    }

    fn add_canonical_auto_param(kernel: &mut Kernel) -> (NameId, NameId, NameId) {
        let anonymous = kernel.anon();
        let lean = kernel.name_str(anonymous, "Lean");
        let syntax = kernel.name_str(lean, "Syntax");
        let tactic = kernel.name_str(anonymous, "testTactic");
        let auto_param = kernel.name_str(anonymous, "autoParam");
        let universe = kernel.name_str(anonymous, "u");
        let alpha = kernel.name_str(anonymous, "alpha");
        let tactic_binder = kernel.name_str(anonymous, "tactic");
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let syntax_sort = kernel.sort(one);
        kernel
            .add_declaration(Declaration::Axiom {
                name: syntax,
                uparams: vec![],
                ty: syntax_sort,
            })
            .expect("Lean.Syntax axiom must admit for the isolated control");
        let syntax_const = kernel.const_(syntax, vec![]);
        kernel
            .add_declaration(Declaration::Axiom {
                name: tactic,
                uparams: vec![],
                ty: syntax_const,
            })
            .expect("test tactic axiom must admit for the isolated control");
        let u = kernel.level_param(universe);
        let sort_u = kernel.sort(u);
        let result_sort = kernel.sort(u);
        let auto_type_inner = kernel.pi(
            tactic_binder,
            syntax_const,
            result_sort,
            BinderInfo::Default,
        );
        let auto_type = kernel.pi(alpha, sort_u, auto_type_inner, BinderInfo::Default);
        let result = kernel.bvar(1);
        let auto_value_inner = kernel.lam(tactic_binder, syntax_const, result, BinderInfo::Default);
        let auto_value = kernel.lam(alpha, sort_u, auto_value_inner, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: auto_param,
                uparams: vec![universe],
                ty: auto_type,
                value: auto_value,
                hint: ReducibilityHint::Abbrev,
            })
            .expect("canonical autoParam must admit");
        (auto_param, syntax, tactic)
    }

    fn saturated_auto_param(kernel: &mut Kernel, auto_param: NameId, tactic: NameId) -> ExprId {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let auto = kernel.const_(auto_param, vec![one]);
        let prop = kernel.sort_zero();
        let with_type = kernel.app(auto, prop);
        let tactic = kernel.const_(tactic, vec![]);
        kernel.app(with_type, tactic)
    }

    fn export(kernel: &Kernel) -> Result<String, ExportError> {
        kernel.render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
    }

    #[test]
    fn a_well_formed_environment_exports() {
        let kernel = kernel_with_logic();
        let stream = export(&kernel).expect("the logic prelude must export");
        assert!(stream.lines().count() > 20);
        assert!(stream.starts_with("{\"meta\":{\"exporter\":{\"name\":\"lean4export\""));
    }

    #[test]
    fn a_root_export_keeps_dependencies_and_excludes_unrelated_declarations() {
        let mut kernel = kernel_with_logic();
        let anonymous = kernel.anon();
        let dependency = kernel.name_str(anonymous, "axeyum.export.selected_dependency");
        let unrelated = kernel.name_str(anonymous, "axeyum.export.unrelated");
        let target = kernel.name_str(anonymous, "axeyum.export.selected_target");
        let prop = kernel.sort_zero();
        kernel
            .add_declaration(Declaration::Axiom {
                name: dependency,
                uparams: Vec::new(),
                ty: prop,
            })
            .expect("a proposition constant is admissible");
        kernel
            .add_declaration(Declaration::Axiom {
                name: unrelated,
                uparams: Vec::new(),
                ty: prop,
            })
            .expect("the unrelated proposition constant is admissible");
        let value = kernel.const_(dependency, Vec::new());
        kernel
            .add_declaration(Declaration::Definition {
                name: target,
                uparams: Vec::new(),
                ty: prop,
                value,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("the selected target is admissible");

        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
            .expect("the selected closure must export");
        assert!(stream.contains("selected_target"), "{stream}");
        assert!(stream.contains("selected_dependency"), "{stream}");
        assert!(!stream.contains("unrelated"), "{stream}");
    }

    #[test]
    fn a_root_export_keeps_implicit_string_literal_bootstrap_dependencies() {
        let mut kernel = kernel_with_logic();
        let anonymous = kernel.anon();
        let string = kernel.name_str(anonymous, "String");
        let char_ = kernel.name_str(anonymous, "Char");
        let list = kernel.name_str(anonymous, "List");
        let of_list = kernel.name_str(string, "ofList");
        let char_of_nat = kernel.name_str(char_, "ofNat");
        let target = kernel.name_str(anonymous, "StringLiteralRoot");
        let prop = kernel.sort_zero();
        for name in [string, char_, list, of_list, char_of_nat] {
            kernel.env.insert_unchecked(Declaration::Axiom {
                name,
                uparams: Vec::new(),
                ty: prop,
            });
        }
        let literal = kernel.lit(Lit::Str("root payload".to_owned()));
        kernel.env.insert_unchecked(Declaration::Definition {
            name: target,
            uparams: Vec::new(),
            ty: prop,
            value: literal,
            hint: ReducibilityHint::Regular(0),
        });

        let stream = kernel
            .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
            .expect("the semantic literal dependencies must form a selected closure");
        let closure = kernel.declaration_dependency_closure(target);
        for dependency in [string, char_, list, of_list, char_of_nat] {
            assert!(closure.contains(&dependency));
        }
        for component in ["String", "Char", "List", "ofList", "ofNat", "Nat"] {
            assert!(
                stream.contains(&format!("\"str\":\"{component}\"")),
                "{component}"
            );
        }
    }

    #[test]
    fn checked_auto_param_type_normalization_drops_only_the_tactic_closure() {
        let mut kernel = kernel_with_logic();
        let (auto_param, syntax, tactic) = add_canonical_auto_param(&mut kernel);
        let anonymous = kernel.anon();
        let helper = kernel.name_str(anonymous, "AutoParamHelper");
        let binder = kernel.name_str(anonymous, "p");
        let annotated = saturated_auto_param(&mut kernel, auto_param, tactic);
        let prop = kernel.sort_zero();
        let helper_type = kernel.pi(binder, annotated, prop, BinderInfo::Default);
        let body = kernel.bvar(0);
        let helper_value = kernel.lam(binder, prop, body, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name: helper,
                uparams: vec![],
                ty: helper_type,
                value: helper_value,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("the source helper must admit by autoParam reduction");

        let exact = kernel
            .root_declaration_closure(&[helper])
            .expect("exact closure must exist");
        assert!(exact.contains(&auto_param));
        assert!(exact.contains(&syntax));
        assert!(exact.contains(&tactic));

        let (stream, report) = kernel
            .render_lean4export_ndjson_roots_checked_auto_param_types(
                &Lean4ExportMetadata::axeyum("4.30.0"),
                &[helper],
            )
            .expect("canonical type-only normalization must export");
        assert_eq!(report.normalized_declarations, ["AutoParamHelper"]);
        assert_eq!(report.rewritten_occurrences, 1);
        assert!(stream.contains("AutoParamHelper"));
        assert!(!stream.contains("autoParam"));
        assert!(!stream.contains("testTactic"));
        assert!(!stream.contains("Syntax"));
    }

    #[test]
    fn checked_auto_param_normalization_rejects_a_same_named_wrong_body() {
        let mut kernel = kernel_with_logic();
        let (auto_param, _, tactic) = add_canonical_auto_param(&mut kernel);
        let Declaration::Definition { value, .. } = kernel
            .environment()
            .get(auto_param)
            .expect("autoParam exists")
            .clone()
        else {
            unreachable!()
        };
        let wrong = match kernel.expr_node(value).clone() {
            ExprNode::Lam(name, ty, body, info) => {
                let wrong_body = match kernel.expr_node(body).clone() {
                    ExprNode::Lam(inner_name, inner_ty, _, inner_info) => {
                        let wrong_result = kernel.bvar(0);
                        kernel.lam(inner_name, inner_ty, wrong_result, inner_info)
                    }
                    _ => unreachable!(),
                };
                kernel.lam(name, ty, wrong_body, info)
            }
            _ => unreachable!(),
        };
        let mut declaration = kernel.environment().get(auto_param).unwrap().clone();
        if let Declaration::Definition { value, .. } = &mut declaration {
            *value = wrong;
        }
        kernel.env.insert_unchecked(declaration);
        let anonymous = kernel.anon();
        let root = kernel.name_str(anonymous, "WrongAutoParamRoot");
        let annotated = saturated_auto_param(&mut kernel, auto_param, tactic);
        kernel.env.insert_unchecked(Declaration::Axiom {
            name: root,
            uparams: vec![],
            ty: annotated,
        });

        assert!(matches!(
            kernel.root_declaration_closure_checked_auto_param_types(&[root]),
            Err(ExportError::AutoParamContract { .. })
        ));
    }

    #[test]
    fn checked_auto_param_normalization_does_not_rewrite_values() {
        let mut kernel = kernel_with_logic();
        let (auto_param, _, tactic) = add_canonical_auto_param(&mut kernel);
        let anonymous = kernel.anon();
        let root = kernel.name_str(anonymous, "AutoParamValueRoot");
        let value = saturated_auto_param(&mut kernel, auto_param, tactic);
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let ty = kernel.sort(one);
        kernel
            .add_declaration(Declaration::Definition {
                name: root,
                uparams: vec![],
                ty,
                value,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("value-position annotation must admit in the source");

        let (closure, report) = kernel
            .root_declaration_closure_checked_auto_param_types(&[root])
            .expect("value-position annotation remains exact");
        assert!(closure.contains(&auto_param));
        assert!(closure.contains(&tactic));
        assert!(report.normalized_declarations.is_empty());
        assert_eq!(report.rewritten_occurrences, 0);
    }

    #[test]
    fn checked_auto_param_binder_normalization_rewrites_only_lambda_domains() {
        let mut kernel = kernel_with_logic();
        let (auto_param, _, tactic) = add_canonical_auto_param(&mut kernel);
        let anonymous = kernel.anon();
        let binder = kernel.name_str(anonymous, "p");
        let annotated = saturated_auto_param(&mut kernel, auto_param, tactic);
        let body_annotation = annotated;
        let source = kernel.lam(binder, annotated, body_annotation, BinderInfo::Default);
        let mut memo = BTreeMap::new();
        let mut rewritten = BTreeSet::new();
        let normalized = kernel.normalize_auto_param_binder_annotations(
            source,
            auto_param,
            &mut memo,
            &mut rewritten,
        );
        let ExprNode::Lam(_, domain, body, _) = kernel.expr_node(normalized) else {
            panic!("normalization must preserve the lambda")
        };
        assert!(matches!(kernel.expr_node(*domain), ExprNode::Sort(_)));
        assert_eq!(
            *body, body_annotation,
            "a value-position gadget stays exact"
        );
        assert_eq!(rewritten.len(), 1);
        assert!(kernel.def_eq(source, normalized));
    }

    #[test]
    fn a_root_export_keeps_an_inductive_unit_atomic() {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
        let stream = kernel
            .render_lean4export_ndjson_roots(
                &Lean4ExportMetadata::axeyum("4.30.0"),
                &[logic.true_intro],
            )
            .expect("a constructor root must export its complete family");
        assert_eq!(stream.matches("\"inductive\"").count(), 1, "{stream}");
        assert!(stream.contains("\"str\":\"True\""), "{stream}");
        assert!(stream.contains("\"str\":\"intro\""), "{stream}");
        assert!(stream.contains("\"str\":\"rec\""), "{stream}");
        assert!(!stream.contains("\"str\":\"False\""), "{stream}");
    }

    #[test]
    fn a_root_export_rejects_empty_and_missing_roots() {
        let mut kernel = kernel_with_logic();
        assert!(matches!(
            kernel.render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[],),
            Err(ExportError::EmptyRoots)
        ));
        let anonymous = kernel.anon();
        let missing = kernel.name_str(anonymous, "axeyum.export.missing");
        assert!(matches!(
            kernel.render_lean4export_ndjson_roots(
                &Lean4ExportMetadata::axeyum("4.30.0"),
                &[missing],
            ),
            Err(ExportError::MissingRoot { .. })
        ));
    }

    #[test]
    fn root_order_and_duplicates_do_not_change_output() {
        let kernel = kernel_with_logic();
        let logic_names: Vec<_> = kernel
            .environment()
            .iter()
            .filter_map(|(&name, declaration)| {
                matches!(declaration, Declaration::Inductive { .. }).then_some(name)
            })
            .take(2)
            .collect();
        assert_eq!(logic_names.len(), 2);
        let metadata = Lean4ExportMetadata::axeyum("4.30.0");
        let first = kernel
            .render_lean4export_ndjson_roots(&metadata, &logic_names)
            .expect("two roots must export");
        let second = kernel
            .render_lean4export_ndjson_roots(
                &metadata,
                &[logic_names[1], logic_names[0], logic_names[1]],
            )
            .expect("root order and duplicates must be irrelevant");
        assert_eq!(first, second);
    }

    #[test]
    fn a_free_variable_is_a_typed_export_error() {
        let mut kernel = kernel_with_logic();
        let anonymous = kernel.anon();
        let name = kernel.name_str(anonymous, "axeyum.export.fvar");
        let ty = kernel.fvar(7);
        kernel.env.insert_unchecked(Declaration::Axiom {
            name,
            uparams: Vec::new(),
            ty,
        });
        assert!(matches!(
            export(&kernel),
            Err(ExportError::FreeVariable { .. })
        ));
    }

    /// The escapes are Lean's `Lean.Json.escapeAux`, not Rust's and not serde's.
    /// Lean gives a short escape to exactly four characters -- quote, backslash,
    /// newline and carriage return -- and writes every other character below
    /// `0x20` as `\u00xx` with lowercase hex digits. Tab, backspace and form
    /// feed are therefore the six-character forms, not `\t`, `\b` and
    /// `\f`. A stream using the short forms would parse the same and would not
    /// be byte-identical to lean4export's, which is the only thing a round-trip
    /// gate can compare.
    #[test]
    fn a_string_literal_is_emitted_with_lean_s_own_json_escapes() {
        let mut kernel = kernel_with_logic();
        let anonymous = kernel.anon();
        let name = kernel.name_str(anonymous, "axeyum.export.str");
        let ty = kernel.lit(Lit::Str(
            "a\"b\\c\nd\re\tf\u{8}g\u{c}h\u{0}i\u{7f}j\u{1f642}".to_owned(),
        ));
        kernel.env.insert_unchecked(Declaration::Axiom {
            name,
            uparams: Vec::new(),
            ty,
        });
        let stream = export(&kernel).expect("a string literal is exportable");
        let expected = concat!(
            "\"strVal\":\"a\\\"b\\\\c\\nd\\re",
            "\\u0009f\\u0008g\\u000ch\\u0000i",
        );
        assert!(stream.contains(expected), "{stream}");
        // `0x7f` and astral scalars are at or above `0x20`: Lean emits them raw.
        assert!(stream.contains("i\u{7f}j\u{1f642}\""), "{stream}");
    }

    #[test]
    fn a_recursor_outside_lean_s_naming_is_a_typed_export_error() {
        let mut kernel = kernel_with_logic();
        let anonymous = kernel.anon();
        let name = kernel.name_str(anonymous, "stray");
        let ty = kernel.sort_zero();
        kernel.env.insert_unchecked(Declaration::Recursor {
            name,
            uparams: Vec::new(),
            ty,
            rec_rules: Vec::new(),
            num_motives: 1,
            num_minors: 0,
            num_params: 0,
            num_indices: 0,
        });
        assert!(matches!(
            export(&kernel),
            Err(ExportError::UnclaimedRecursor { .. })
        ));
    }

    #[test]
    fn a_half_quotient_package_is_a_typed_export_error() {
        let mut kernel = kernel_with_logic();
        let anonymous = kernel.anon();
        let name = kernel.name_str(anonymous, "Quot");
        let ty = kernel.sort_zero();
        kernel.env.insert_unchecked(Declaration::Quotient {
            name,
            uparams: Vec::new(),
            ty,
            kind: QuotKind::Type,
        });
        assert!(matches!(
            export(&kernel),
            Err(ExportError::IncompleteQuotientPackage { present: 1 })
        ));
    }

    #[test]
    fn a_dependency_cycle_is_a_typed_export_error() {
        let mut kernel = kernel_with_logic();
        let anonymous = kernel.anon();
        let first = kernel.name_str(anonymous, "axeyum.export.cycle.a");
        let second = kernel.name_str(anonymous, "axeyum.export.cycle.b");
        let to_second = kernel.const_(second, Vec::new());
        let to_first = kernel.const_(first, Vec::new());
        kernel.env.insert_unchecked(Declaration::Axiom {
            name: first,
            uparams: Vec::new(),
            ty: to_second,
        });
        kernel.env.insert_unchecked(Declaration::Axiom {
            name: second,
            uparams: Vec::new(),
            ty: to_first,
        });
        assert!(matches!(
            export(&kernel),
            Err(ExportError::DependencyCycle { .. })
        ));
    }

    #[test]
    fn a_missing_selected_dependency_is_a_typed_export_error() {
        let mut kernel = kernel_with_logic();
        let anonymous = kernel.anon();
        let root = kernel.name_str(anonymous, "axeyum.export.missing_dependency.root");
        let missing = kernel.name_str(anonymous, "axeyum.export.missing_dependency.absent");
        let ty = kernel.const_(missing, Vec::new());
        kernel.env.insert_unchecked(Declaration::Axiom {
            name: root,
            uparams: Vec::new(),
            ty,
        });
        assert!(matches!(
            kernel
                .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[root],),
            Err(ExportError::MissingDependency { .. })
        ));
    }

    #[test]
    fn explicit_theorem_leaf_cuts_only_its_proof_dependencies() {
        let mut kernel = kernel_with_logic();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude is cached");
        let anonymous = kernel.anon();
        let true_ty = kernel.const_(logic.true_, vec![]);
        let true_intro = kernel.const_(logic.true_intro, vec![]);
        let theorem = |kernel: &mut Kernel, label: &str, proof: ExprId| {
            let name = kernel.name_str(anonymous, label);
            kernel
                .add_declaration(Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty: true_ty,
                    value: proof,
                })
                .expect("the theorem control checks");
            name
        };
        let hidden = theorem(&mut kernel, "LeafControl.hidden", true_intro);
        let hidden_const = kernel.const_(hidden, vec![]);
        let leaf = theorem(&mut kernel, "LeafControl.leaf", hidden_const);
        let leaf_const = kernel.const_(leaf, vec![]);
        let root = theorem(&mut kernel, "LeafControl.root", leaf_const);
        let other = theorem(&mut kernel, "LeafControl.unreachable", true_intro);

        let full = kernel
            .root_declaration_closure(&[root])
            .expect("the full proof closure exists");
        assert!(full.contains(&hidden));
        let cut = kernel
            .root_declaration_closure_with_theorem_leaves(&[root], &[leaf])
            .expect("the explicit reachable theorem leaf cuts its proof");
        assert!(cut.contains(&root));
        assert!(cut.contains(&leaf));
        assert!(!cut.contains(&hidden));
        let leaf_at = cut.iter().position(|name| *name == leaf).unwrap();
        let root_at = cut.iter().position(|name| *name == root).unwrap();
        assert!(leaf_at < root_at);

        assert!(matches!(
            kernel.root_declaration_closure_with_theorem_leaves(&[root], &[leaf, leaf]),
            Err(ExportError::DuplicateTheoremLeaf { .. })
        ));
        assert!(matches!(
            kernel.root_declaration_closure_with_theorem_leaves(&[root], &[logic.true_]),
            Err(ExportError::LeafIsNotTheorem { .. })
        ));
        assert!(matches!(
            kernel.root_declaration_closure_with_theorem_leaves(&[root], &[other]),
            Err(ExportError::UnreachableTheoremLeaf { .. })
        ));
        let missing = kernel.name_str(anonymous, "LeafControl.missing");
        assert!(matches!(
            kernel.root_declaration_closure_with_theorem_leaves(&[root], &[missing]),
            Err(ExportError::MissingRoot { .. })
        ));
    }
}
