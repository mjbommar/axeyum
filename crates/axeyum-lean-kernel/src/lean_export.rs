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
        let order = self.order_units(self.export_units()?)?;
        let mut emitter = Emitter {
            kernel: self,
            writer,
            names: BTreeMap::new(),
            levels: BTreeMap::new(),
            expressions: BTreeMap::new(),
            next_name: 1,
            next_level: 1,
            next_expression: 0,
        };
        emitter.metadata(metadata)?;
        for unit in order {
            emitter.unit(&unit)?;
        }
        Ok(())
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
    fn order_units(&self, units: Vec<Unit>) -> Result<Vec<Unit>, ExportError> {
        let mut owner: BTreeMap<NameId, usize> = BTreeMap::new();
        for (index, unit) in units.iter().enumerate() {
            for member in unit.members() {
                owner.insert(member, index);
            }
        }
        let dependencies: Vec<Vec<usize>> = units
            .iter()
            .enumerate()
            .map(|(index, unit)| {
                let mut referenced = BTreeSet::new();
                for member in unit.members() {
                    for constant in self.member_constants(member) {
                        if let Some(&other) = owner.get(&constant)
                            && other != index
                        {
                            referenced.insert(other);
                        }
                    }
                }
                referenced.into_iter().collect()
            })
            .collect();

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
    fn member_constants(&self, member: NameId) -> BTreeSet<NameId> {
        let mut constants = BTreeSet::new();
        let Some(declaration) = self.environment().get(member) else {
            return constants;
        };
        let mut roots = vec![declaration.ty()];
        if let Some(value) = declaration.value() {
            roots.push(value);
        }
        if let Declaration::Recursor { rec_rules, .. } = declaration {
            roots.extend(rec_rules.iter().map(|rule| rule.value));
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
                ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
            }
        }
        constants
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
    pub(crate) fn is_k_like_inductive(&self, family: NameId) -> bool {
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
        let ty = self.expression(declaration.ty(), &label)?;
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
            let ty = self.expression(ty, &label)?;
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
            let ty = self.expression(ty, &label)?;
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
            for rule in &rec_rules {
                let rhs = self.expression(rule.value, &label)?;
                let constructor = self.name(rule.ctor_name)?;
                rules.push(format!(
                    "{{\"ctor\":{constructor},\"nfields\":{},\"rhs\":{rhs}}}",
                    rule.num_fields
                ));
            }
            let uparams = self.name_list(&uparams)?;
            let ty = self.expression(ty, &label)?;
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
    use super::{ExportError, Lean4ExportMetadata};
    use crate::{Declaration, Kernel, Lit, QuotKind, build_logic_prelude};

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
}
