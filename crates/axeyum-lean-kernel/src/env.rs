//! The global environment and non-inductive declaration layer (ADR-0036,
//! slice 3).
//!
//! A Lean kernel checks terms relative to an *environment*: a set of global
//! declarations (axioms, definitions, theorems, opaque constants) that a
//! `Const` term can reference. This module ports nanoda's `declar.rs`/`env.rs`
//! for the **non-inductive** fragment, adapted to axeyum's interned
//! lifetime-free handles.
//!
//! ## Scope
//!
//! In scope: [`ReducibilityHint`], the four non-inductive [`Declaration`]
//! kinds ([`Declaration::Axiom`], [`Declaration::Definition`],
//! [`Declaration::Theorem`], [`Declaration::Opaque`]), and the
//! [`Environment`] map. The trusted admission gate (`add_declaration`),
//! universe instantiation, `Const` inference, δ-unfolding, and the lazy-delta
//! step live on [`super::Kernel`] (see `tc.rs`).
//!
//! The inductive, constructor, and recursor variants plus ι-reduction are now
//! implemented by `inductive.rs`. Projection inference, constructor reduction,
//! and structure eta use the checked inductive metadata recorded here.
//! **Deferred to later slices**: `Quotient` reduction; unsupported semantic
//! paths reject rather than guess.
//!
//! ## Determinism
//!
//! The [`Environment`] stores declarations in a [`std::collections::BTreeMap`]
//! keyed by [`NameId`], so iteration order is the (stable) id order — no
//! hash-map iteration order is ever observable (determinism rule).

use std::collections::BTreeMap;

use crate::expr::ExprId;
use crate::name::NameId;

/// Reducibility hints accompanying definitions; they drive **which** side a
/// lazy-delta step unfolds when comparing two applied definitions, so that
/// equality checking unfolds the "greater" definition to bring the two sides
/// closer. Ported from nanoda's `ReducibilityHint`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReducibilityHint {
    /// An opaque hint: never preferred for unfolding during delta.
    Opaque,
    /// A regular definition carrying its computed height (the maximal
    /// definition-call depth of its value). Higher height unfolds first.
    Regular(u16),
    /// An abbreviation: always preferred for unfolding during delta.
    Abbrev,
}

impl ReducibilityHint {
    /// Whether `self` is "less than" `other` for delta unfolding: during
    /// definitional equality we unfold the **greater** of two definitions
    /// first. Ported line-for-line from nanoda's `ReducibilityHint::is_lt`.
    #[must_use]
    pub(crate) fn is_lt(self, other: Self) -> bool {
        use ReducibilityHint::{Abbrev, Opaque, Regular};
        // Order-sensitive (matches nanoda's `is_lt`): these arms are evaluated
        // top-down, so the `(_, Opaque)`/`(Abbrev, _)` group must precede the
        // `(Opaque, _)`/`(_, Abbrev)` group.
        match (self, other) {
            (_, Opaque) | (Abbrev, _) => false,
            (Opaque, _) | (_, Abbrev) => true,
            (Regular(h1), Regular(h2)) => h1 < h2,
        }
    }
}

/// A single ι-reduction (recursor computation) rule, ported from nanoda's
/// `RecRule`.
///
/// When a recursor's major premise WHNFs to an application of `ctor_name` to
/// `num_fields` field arguments, the recursor application reduces by applying
/// this rule's [`value`](RecRule::value) (the ι-reduction RHS) to the
/// recursor's prefix arguments, the constructor's fields, and any trailing
/// arguments. `num_fields` is the constructor's field count **excluding the
/// parameters** (the ι-rule strips the leading parameters; the recursor's index
/// arguments sit before the major and are not consumed by the rule value).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecRule {
    /// The constructor this rule fires for.
    pub ctor_name: NameId,
    /// The constructor's field count (telescope size). For the non-parametric,
    /// non-indexed scope this is the full number of constructor arguments.
    pub num_fields: u16,
    /// The ι-reduction right-hand side: a closed `λ`-telescope over the motive,
    /// the minor premises, and the constructor's fields, whose body applies the
    /// matching minor premise to the fields.
    pub value: ExprId,
}

/// A checked global declaration.
///
/// Every declaration carries a `name`, a list of universe parameter names
/// (`uparams`), and a closed type (`ty`). Definitions/theorems/opaque
/// constants additionally carry a closed `value`. Definitions carry a
/// [`ReducibilityHint`] driving lazy-delta side choice.
///
/// The inductive layer (ADR-0036, through slice 7) adds
/// [`Declaration::Inductive`], [`Declaration::Constructor`], and
/// [`Declaration::Recursor`], supporting **parametric**, **recursive**
/// (non-indexed), and **non-recursive indexed** inductive types (enums,
/// structures, `Nat`/`List`/`Prod`/`Sum`, and `Eq`). Recursive constructors on
/// an indexed family, reflexive/nested fields, and mutual inductives are
/// deferred to later slices and rejected explicitly by the admission gate
/// rather than guessed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declaration {
    /// `axiom name : ty` — an asserted constant with no definitional value.
    /// Axioms never δ-unfold.
    Axiom {
        /// The declaration's name.
        name: NameId,
        /// The universe parameter names this declaration is polymorphic over.
        uparams: Vec<NameId>,
        /// The declaration's (closed) type.
        ty: ExprId,
    },
    /// `def name : ty := value` — a definition that may δ-unfold to `value`.
    Definition {
        /// The declaration's name.
        name: NameId,
        /// The universe parameter names this declaration is polymorphic over.
        uparams: Vec<NameId>,
        /// The declaration's (closed) type.
        ty: ExprId,
        /// The declaration's (closed) value.
        value: ExprId,
        /// The reducibility hint driving lazy-delta side choice.
        hint: ReducibilityHint,
    },
    /// `theorem name : ty := value` — like a definition, but its proof value
    /// is treated as [`ReducibilityHint::Opaque`] during lazy-delta (so two
    /// theorems are compared structurally before unfolding).
    Theorem {
        /// The declaration's name.
        name: NameId,
        /// The universe parameter names this declaration is polymorphic over.
        uparams: Vec<NameId>,
        /// The declaration's (closed) type.
        ty: ExprId,
        /// The declaration's (closed) proof value.
        value: ExprId,
    },
    /// `opaque name : ty := value` — its value is checked at admission time
    /// but is **never** δ-unfolded for definitional equality.
    Opaque {
        /// The declaration's name.
        name: NameId,
        /// The universe parameter names this declaration is polymorphic over.
        uparams: Vec<NameId>,
        /// The declaration's (closed) type.
        ty: ExprId,
        /// The declaration's (closed) value (checked, but never unfolded).
        value: ExprId,
    },
    /// An inductive type `I : ty` (a telescope `Π params indices, Sort u`), with
    /// its constructor names. Admitted only through
    /// [`super::Kernel::add_inductive`](crate::Kernel::add_inductive).
    Inductive {
        /// The inductive type's name.
        name: NameId,
        /// The universe parameter names the type is polymorphic over.
        uparams: Vec<NameId>,
        /// The inductive's closed type: a parameter/index telescope ending in
        /// a `Sort`.
        ty: ExprId,
        /// Number of leading parameter binders fixed across the family.
        /// Projection inference instantiates these from the projected value's
        /// type before walking constructor fields.
        num_params: u16,
        /// Number of index binders after the parameters. Projection inference
        /// validates the projected value's complete parameter/index spine.
        num_indices: u16,
        /// Whether any checked constructor has a direct recursive field.
        /// Structure eta is legal only when this is false, matching Lean's
        /// `is_non_rec_structure` predicate.
        is_recursive: bool,
        /// The names of this type's constructors, in declaration order.
        ctor_names: Vec<NameId>,
    },
    /// A constructor `c : Π params fields, I params indices` of inductive
    /// `inductive`. Field types may mention `I` as a **direct recursive field**
    /// (only on a non-indexed family).
    Constructor {
        /// The constructor's name.
        name: NameId,
        /// The universe parameter names (shared with the parent inductive).
        uparams: Vec<NameId>,
        /// The constructor's (closed) type.
        ty: ExprId,
        /// The parent inductive type's name.
        inductive: NameId,
        /// The constructor's 0-based index within the inductive.
        idx: u16,
        /// The number of constructor fields (telescope size; no params here).
        num_fields: u16,
    },
    /// A recursor
    /// `I.rec : Π params {motive} (minors…) (indices) (major), motive indices major`,
    /// generated by [`super::Kernel::add_inductive`](crate::Kernel::add_inductive)
    /// for a checked inductive, together with its ι-reduction
    /// [`RecRule`]s.
    Recursor {
        /// The recursor's name (`I.rec`).
        name: NameId,
        /// The recursor's universe parameters. Large-eliminating recursors use
        /// the motive's elimination level followed by the inductive's universe
        /// parameters. A potentially-`Prop`, non-subsingleton recursor omits
        /// that fresh level and contains only the inductive's parameters because
        /// its motive universe is fixed at zero.
        uparams: Vec<NameId>,
        /// The recursor's (closed) type.
        ty: ExprId,
        /// The ι-reduction rules, one per constructor.
        rec_rules: Vec<RecRule>,
        /// The number of motives (always `1` in this non-mutual slice).
        num_motives: u16,
        /// The number of minor premises (one per constructor).
        num_minors: u16,
        /// The number of parameters (fixed across the family).
        num_params: u16,
        /// The number of indices (non-zero for an indexed family, e.g. `Eq`).
        num_indices: u16,
    },
}

impl Declaration {
    /// The index of the major premise in the recursor's argument telescope:
    /// `num_params + num_motives + num_minors + num_indices`. Mirrors nanoda's
    /// `RecursorData::major_idx`.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not a [`Declaration::Recursor`].
    #[must_use]
    pub(crate) fn major_idx(&self) -> usize {
        match self {
            Declaration::Recursor {
                num_params,
                num_motives,
                num_minors,
                num_indices,
                ..
            } => (*num_params + *num_motives + *num_minors + *num_indices) as usize,
            _ => panic!("major_idx called on a non-recursor declaration"),
        }
    }
}

impl Declaration {
    /// The declaration's name.
    #[must_use]
    pub fn name(&self) -> NameId {
        match self {
            Declaration::Axiom { name, .. }
            | Declaration::Definition { name, .. }
            | Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Inductive { name, .. }
            | Declaration::Constructor { name, .. }
            | Declaration::Recursor { name, .. } => *name,
        }
    }

    /// The declaration's universe parameter names.
    #[must_use]
    pub fn uparams(&self) -> &[NameId] {
        match self {
            Declaration::Axiom { uparams, .. }
            | Declaration::Definition { uparams, .. }
            | Declaration::Theorem { uparams, .. }
            | Declaration::Opaque { uparams, .. }
            | Declaration::Inductive { uparams, .. }
            | Declaration::Constructor { uparams, .. }
            | Declaration::Recursor { uparams, .. } => uparams,
        }
    }

    /// The declaration's (closed) type.
    #[must_use]
    pub fn ty(&self) -> ExprId {
        match self {
            Declaration::Axiom { ty, .. }
            | Declaration::Definition { ty, .. }
            | Declaration::Theorem { ty, .. }
            | Declaration::Opaque { ty, .. }
            | Declaration::Inductive { ty, .. }
            | Declaration::Constructor { ty, .. }
            | Declaration::Recursor { ty, .. } => *ty,
        }
    }

    /// The declaration's definitional value, if it has one (definitions,
    /// theorems, opaque constants). Axioms and the inductive-layer kinds
    /// (inductives/constructors/recursors) return `None`.
    #[must_use]
    pub fn value(&self) -> Option<ExprId> {
        match self {
            Declaration::Axiom { .. }
            | Declaration::Inductive { .. }
            | Declaration::Constructor { .. }
            | Declaration::Recursor { .. } => None,
            Declaration::Definition { value, .. }
            | Declaration::Theorem { value, .. }
            | Declaration::Opaque { value, .. } => Some(*value),
        }
    }

    /// The value to substitute when **δ-unfolding** this declaration.
    ///
    /// Returns `Some(value)` only for declarations that unfold for
    /// definitional equality — `Definition` and `Theorem`. `Axiom` (no value)
    /// and `Opaque` (value checked but never unfolded) return `None`,
    /// matching nanoda's `get_declar_val`.
    #[must_use]
    pub(crate) fn delta_value(&self) -> Option<ExprId> {
        match self {
            Declaration::Definition { value, .. } | Declaration::Theorem { value, .. } => {
                Some(*value)
            }
            Declaration::Axiom { .. }
            | Declaration::Opaque { .. }
            | Declaration::Inductive { .. }
            | Declaration::Constructor { .. }
            | Declaration::Recursor { .. } => None,
        }
    }

    /// The reducibility hint used to pick the unfolding side in lazy-delta,
    /// for declarations that unfold. `Theorem` is treated as
    /// [`ReducibilityHint::Opaque`] (matching nanoda's `get_applied_def`);
    /// `Axiom`/`Opaque` return `None` because they never unfold.
    #[must_use]
    pub(crate) fn delta_hint(&self) -> Option<ReducibilityHint> {
        match self {
            Declaration::Definition { hint, .. } => Some(*hint),
            Declaration::Theorem { .. } => Some(ReducibilityHint::Opaque),
            Declaration::Axiom { .. }
            | Declaration::Opaque { .. }
            | Declaration::Inductive { .. }
            | Declaration::Constructor { .. }
            | Declaration::Recursor { .. } => None,
        }
    }
}

/// The global environment: a deterministic map from [`NameId`] to
/// [`Declaration`].
///
/// Backed by a [`BTreeMap`] so iteration order is id order (determinism rule).
/// Declarations are admitted only through [`super::Kernel::add_declaration`],
/// which type-checks them first (the trusted kernel gate).
#[derive(Debug, Default, Clone)]
pub struct Environment {
    declars: BTreeMap<NameId, Declaration>,
}

impl Environment {
    /// An empty environment.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up the declaration named `name`, if any.
    #[must_use]
    pub fn get(&self, name: NameId) -> Option<&Declaration> {
        self.declars.get(&name)
    }

    /// Whether a declaration named `name` is already present.
    #[must_use]
    pub fn contains(&self, name: NameId) -> bool {
        self.declars.contains_key(&name)
    }

    /// The number of admitted declarations.
    #[must_use]
    pub fn len(&self) -> usize {
        self.declars.len()
    }

    /// Whether the environment holds no declarations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.declars.is_empty()
    }

    /// Iterate declarations in deterministic (id) order.
    pub fn iter(&self) -> impl Iterator<Item = (&NameId, &Declaration)> {
        self.declars.iter()
    }

    /// Look up `name` as a [`Declaration::Recursor`], returning its rec-rules,
    /// universe parameters, and premise counts if present.
    #[must_use]
    pub(crate) fn get_recursor(&self, name: NameId) -> Option<&Declaration> {
        match self.declars.get(&name) {
            Some(d @ Declaration::Recursor { .. }) => Some(d),
            _ => None,
        }
    }

    /// Insert a declaration **without** type-checking it.
    ///
    /// This is the low-level, untrusted insert; callers must have already
    /// validated the declaration. Use [`super::Kernel::add_declaration`] for
    /// the trusted, type-checked admission path.
    pub(crate) fn insert_unchecked(&mut self, decl: Declaration) {
        self.declars.insert(decl.name(), decl);
    }

    /// Remove a declaration by name (used to roll back a partially-admitted
    /// inductive when a later constructor or the recursor fails to check).
    pub(crate) fn remove_unchecked(&mut self, name: NameId) {
        self.declars.remove(&name);
    }
}

#[cfg(test)]
mod env_tests;
