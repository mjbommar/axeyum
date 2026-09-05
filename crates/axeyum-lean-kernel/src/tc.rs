//! Type-theory core: WHNF reduction, definitional equality, and type inference
//! over a global declaration [`Environment`](crate::Environment) for the
//! non-inductive fragment of the Lean kernel (ADR-0036, slice 3).
//!
//! This is the **trusted core**: a wrong type-checker wrongly accepts proofs.
//! The algorithm is ported faithfully from nanoda's `tc.rs`/`env.rs` for the
//! in-scope fragment — `Sort`, `FVar` (locals), `App`, `Lam`, `Pi`, `Let`,
//! `BVar`, and now `Const` referencing non-inductive declarations — and it
//! stops at the still-deferred boundary with an explicit error, never a guess.
//!
//! ## Scope
//!
//! In scope: beta reduction, zeta/let reduction, **δ-unfolding** of
//! `Definition`/`Theorem` constants, universe instantiation, the lazy
//! structural definitional-equality algorithm with nanoda's
//! **lazy-delta step** (height-driven side choice + same-const short-circuit),
//! eta-expansion, proof irrelevance, type inference including `Const`, and the
//! trusted [`Kernel::add_declaration`](crate::Kernel::add_declaration)
//! admission gate.
//!
//! Projection inference/reduction, structure eta, inductive/recursor
//! ι-reduction, the fixed quotient package, and both literal profiles (`Nat`
//! arithmetic, ADR-0459; `String` typing and the `String.ofList` expansion,
//! ADR-0366) are implemented. A literal whose reserved bootstrap the environment
//! does not carry is refused by name
//! ([`KernelError::NatLiteralBootstrapMismatch`],
//! [`KernelError::StringLiteralBootstrapMismatch`]) rather than guessed. An
//! unknown `Const` name returns [`KernelError::UnknownConst`].
//! `Opaque` declarations are admitted but never δ-unfold; `Axiom`s never
//! unfold. None of these paths panic.
//!
//! ## How binders are opened
//!
//! nanoda opens a binder by allocating a fresh de Bruijn *level* local (an
//! `FVar` whose node also stores the binder type), instantiating `BVar 0` of
//! the body with it, recursing, then re-abstracting. axeyum's `FVar(u64)`
//! carries only an id, so the binder type/name/info live in a side table — the
//! [`LocalContext`]. Opening a binder:
//!
//! 1. mint a fresh `FVar` id (a monotone counter on the context),
//! 2. record its [`LocalDecl`] (name, type, binder info) in the context,
//! 3. `instantiate` the body's `BVar 0` with that `FVar`,
//! 4. recurse, then `abstract_fvars` the inferred body type back over the
//!    fvar id when a `Pi`/`Lam` result must be rebuilt,
//! 5. pop the decl.
//!
//! This mirrors nanoda's `mk_dbj_level` / `inst` / `abstr_levels` /
//! `replace_dbj_level` exactly, with the side table standing in for the type
//! that nanoda packs into its `Local` node.

use std::collections::HashMap;

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{ExprId, ExprNode, Lit, NatLit};
use crate::level::{LevelId, LevelNode};
use crate::name::NameId;
use crate::{BinderInfo, Kernel};

/// An error from the kernel type-checker.
///
/// All variants are returned, never panicked: the kernel rejects malformed or
/// out-of-scope input deterministically.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelError {
    /// Application of a non-function: the inferred type of the function part of
    /// an `App` did not WHNF to a `Pi`.
    NotAPi {
        /// The (already inferred) type of the function that should have been a
        /// `Pi`.
        got: ExprId,
    },
    /// An expression that should have been a type did not infer/WHNF to a
    /// `Sort` (e.g. a `Lam`/`Pi`/`Let` binder domain that is not a type).
    NotASort {
        /// The inferred type that should have been a `Sort`.
        got: ExprId,
    },
    /// A definitional-equality check failed: `expected` and `got` are not
    /// def-eq (e.g. an argument's type does not match a `Pi` domain, or a
    /// `let` value's type does not match its annotation).
    TypeMismatch {
        /// The type that was required at this position.
        expected: ExprId,
        /// The type that was actually inferred.
        got: ExprId,
    },
    /// A loose `BVar` reached inference: it should have been opened to an
    /// `FVar` under its binder. A well-formed closed term never triggers this.
    LooseBVar {
        /// The de Bruijn index that escaped.
        index: u32,
    },
    /// An `FVar` was encountered that is not bound in the current
    /// [`LocalContext`].
    UnboundFVar {
        /// The free-variable id that was not found.
        id: u64,
    },
    /// A `Const` reached inference but the prior, environment-free slice could
    /// not type it. Retained for back-compatibility; the environment slice
    /// (ADR-0036) now resolves known constants and reports unknown names via
    /// [`KernelError::UnknownConst`] instead.
    UnsupportedConst {
        /// The constant's name id (interned in the owning kernel).
        name: crate::name::NameId,
    },
    /// A `Const` named a declaration that is not present in the environment.
    UnknownConst {
        /// The unresolved constant's name id (interned in the owning kernel).
        name: crate::name::NameId,
    },
    /// A `Const`'s universe-argument count did not match its declaration's
    /// universe-parameter count.
    UniverseArityMismatch {
        /// The constant's name id (interned in the owning kernel).
        name: crate::name::NameId,
        /// The number of universe parameters the declaration expects.
        expected: usize,
        /// The number of universe arguments the `Const` supplied.
        got: usize,
    },
    /// A literal reached inference in an environment with no checked bootstrap
    /// for its kind.
    ///
    /// Retained for back-compatibility only: both literal kinds now report the
    /// *reserved declaration* that was absent or malformed
    /// ([`KernelError::NatLiteralBootstrapMismatch`],
    /// [`KernelError::StringLiteralBootstrapMismatch`]) rather than a bare
    /// "unsupported", so nothing constructs this variant.
    UnsupportedLit,
    /// A Nat literal was used before the checked environment contained the
    /// canonical non-polymorphic `Nat`/`Nat.zero`/`Nat.succ` bootstrap.
    NatLiteralBootstrapMismatch {
        /// The reserved `Nat` name whose checked declaration was absent or
        /// malformed.
        nat: crate::name::NameId,
    },
    /// A String literal was used before the checked environment contained the
    /// canonical `String`/`String.ofList`/`Char`/`Char.ofNat`/`List` bootstrap
    /// (which in turn requires the canonical `Nat` bootstrap).
    ///
    /// Carries the reserved `String` name so a caller can render it; the
    /// individual clause that failed is deliberately *not* reported, because a
    /// partial bootstrap is never stored and no rule fires from one.
    StringLiteralBootstrapMismatch {
        /// The reserved `String` name, interned in the owning kernel. `None`
        /// when the environment has never even heard the name.
        string: Option<crate::name::NameId>,
    },
    /// The inferred type of a projected value did not have the structure name
    /// carried by the `Proj` node as its constant head.
    ProjectionTypeMismatch {
        /// Structure name recorded in the projection node.
        expected: crate::name::NameId,
        /// Complete inferred/WHNF type of the projected value.
        got: ExprId,
    },
    /// A projection's named type was absent or was not an inductive
    /// declaration in the checked environment.
    ProjectionNotInductive {
        /// Invalid structure type name.
        name: crate::name::NameId,
    },
    /// Projection requires an inductive with exactly one constructor.
    ProjectionConstructorCount {
        /// Inductive type named by the projection.
        name: crate::name::NameId,
        /// Number of constructors recorded by its checked declaration.
        got: usize,
    },
    /// The projected value's type did not supply exactly the inductive's
    /// checked parameter-plus-index argument count.
    ProjectionArityMismatch {
        /// Inductive type named by the projection.
        name: crate::name::NameId,
        /// Checked parameter-plus-index count.
        expected: usize,
        /// Application arguments present on the projected value's type.
        got: usize,
    },
    /// A projection selected a field outside the checked constructor field
    /// range. Field indices exclude parameters and are zero-based.
    ProjectionFieldOutOfBounds {
        /// Inductive type named by the projection.
        name: crate::name::NameId,
        /// Requested zero-based field index.
        field_index: u32,
        /// Checked number of non-parameter constructor fields.
        field_count: u16,
    },
    /// Checked structure metadata and the constructor telescope disagreed
    /// while instantiating parameters or walking to the selected field.
    MalformedProjectionConstructor {
        /// Inductive type named by the projection.
        name: crate::name::NameId,
        /// Sole constructor expected to supply the field telescope.
        ctor: crate::name::NameId,
        /// Requested zero-based field index.
        field_index: u32,
    },
    /// A projection attempted to eliminate a proof-valued structure into data.
    /// Lean permits such a projection only when every traversed dependent field
    /// and the selected field are themselves propositions.
    ProjectionFromPropToType {
        /// Inductive type named by the projection.
        name: crate::name::NameId,
        /// Requested zero-based field index.
        field_index: u32,
    },
    /// A declaration with this name already exists in the environment;
    /// re-declaration is rejected.
    DeclarationExists {
        /// The name that was already declared.
        name: crate::name::NameId,
    },
    /// A previously built prelude no longer matches its exact package snapshot.
    PreludePackageConflict {
        /// First missing or changed declaration in the package.
        name: crate::name::NameId,
    },
    /// A requested finite string alphabet cannot be represented by the stable
    /// `u64` namespace key used by the string prelude package registry.
    StringAlphabetSizeOverflow {
        /// Host-sized alphabet cardinality that did not fit the wire key.
        num_chars: usize,
    },
    /// A privileged quotient declaration was sent through the ordinary
    /// single-declaration gate rather than the atomic package gate.
    QuotientPackageRequired {
        /// Quotient declaration that could not be admitted alone.
        name: crate::name::NameId,
    },
    /// Quotient initialization requires exactly four ordered declarations.
    QuotientPackageLength {
        /// Required fixed package length.
        expected: usize,
        /// Supplied package length.
        got: usize,
    },
    /// The environment's `Eq`/`Eq.refl` bootstrap is absent or differs from
    /// the exact Lean kernel contract required before quotient initialization.
    QuotientEqBootstrapMismatch {
        /// First missing or malformed bootstrap declaration.
        name: crate::name::NameId,
    },
    /// A quotient package member occurred under the wrong reserved name or at
    /// the wrong ordered position.
    QuotientPackageNameMismatch {
        /// Zero-based package position.
        index: usize,
        /// Reserved name required at this position.
        expected: crate::name::NameId,
        /// Supplied declaration name.
        got: crate::name::NameId,
    },
    /// A quotient package declaration carried the wrong fixed role.
    QuotientPackageKindMismatch {
        /// Declaration whose role disagreed.
        name: crate::name::NameId,
        /// Required role for this reserved name.
        expected: crate::QuotKind,
        /// Supplied role.
        got: crate::QuotKind,
    },
    /// A quotient package member has the wrong universe-parameter arity or
    /// aliases two parameter positions that must be distinct.
    QuotientUniverseParametersMismatch {
        /// Declaration whose universe parameters disagreed.
        name: crate::name::NameId,
        /// Required number of distinct parameters.
        expected: usize,
        /// Supplied parameter count.
        got: usize,
    },
    /// A quotient declaration's type differs from the independently derived
    /// Lean 4.30 package type (binder display names are ignored).
    QuotientTypeMismatch {
        /// Declaration whose type disagreed.
        name: crate::name::NameId,
    },
    /// One or more reserved quotient names already exist, but the environment
    /// does not contain the complete exact package.
    QuotientPackageConflict {
        /// First conflicting reserved name.
        name: crate::name::NameId,
    },
    /// An attempted mutual-inductive declaration contained no families.
    EmptyInductiveGroup,
    /// A family, constructor, or generated recursor name occurred more than
    /// once inside one ordered mutual-inductive group.
    DuplicateInductiveGroupName {
        /// The repeated group-local declaration name.
        name: crate::name::NameId,
    },
    /// One mutual-inductive family did not expose the shared parameter at the
    /// registered position, or its parameter type was not definitionally equal
    /// to the first family's parameter type.
    MutualInductiveParameterMismatch {
        /// The family whose parameter telescope disagreed.
        family: crate::name::NameId,
        /// Zero-based position in the shared parameter telescope.
        parameter_index: usize,
    },
    /// One mutual-inductive family's result universe was not equivalent to the
    /// first family's result universe after opening parameters and indices.
    MutualInductiveResultUniverseMismatch {
        /// The family whose result universe disagreed.
        family: crate::name::NameId,
    },
    /// Historical M1 policy decline retained for public error-enum compatibility.
    /// TL2.13 M2 no longer returns this result from the native group gate.
    MutualInductiveNotSupported {
        /// Number of families in the declined group.
        family_count: usize,
    },
    /// A generated mutual recursor disagreed with the checked group's owner,
    /// count, rule ordering, or field-count contract.
    MutualRecursorContractMismatch {
        /// Family whose generated recursor contract disagreed.
        family: crate::name::NameId,
    },
    /// A declaration's type or value mentioned a universe parameter that the
    /// declaration does not bind.
    ///
    /// Lean's kernel calls this an `invalid reference to undefined universe
    /// level parameter`. It is not a hygiene rule: `Const(c, us)` substitutes
    /// `us` positionally for `c`'s DECLARED parameters, so a parameter that is
    /// not declared is never substituted at any instantiation site and leaks
    /// into every use as a universe nobody chose.
    UndeclaredUniverseParam {
        /// The declaration that mentioned it.
        declaration: crate::name::NameId,
        /// The universe parameter that is free in the declaration.
        param: crate::name::NameId,
    },
    /// A declaration bound the same universe parameter twice.
    ///
    /// `Const(c, us)` substitutes `us` positionally for `c`'s declared
    /// parameters, so a name that appears twice in the binding list has two
    /// candidate substitutions at every instantiation site and the declaration
    /// does not denote one thing. Lean rejects it; this kernel admitted it
    /// until ADR-1663 (the public conformance corpus's `tut06_bad01` case,
    /// `docs/plan/lean-divergences.md` D2).
    DuplicateUniverseParam {
        /// The declaration that bound it twice.
        declaration: crate::name::NameId,
        /// The universe parameter that appears more than once.
        param: crate::name::NameId,
    },
    /// A declaration's type did not infer/WHNF to a `Sort` (every declaration's
    /// type must itself be a type).
    DeclarationTypeNotASort {
        /// The non-`Sort` type that was inferred for the declaration's type.
        got: ExprId,
    },
    /// A definition/theorem/opaque declaration's value did not type-check to a
    /// type definitionally equal to its declared type.
    DeclarationValueMismatch {
        /// The declaration's declared type.
        declared: ExprId,
        /// The type inferred for the declaration's value.
        inferred: ExprId,
    },
    /// An inductive type's declared type was not a (telescope ending in a)
    /// `Sort`. In this slice (no parameters/indices) the type must be a bare
    /// `Sort`; a `Pi`-headed type is a parametric/indexed inductive, deferred.
    InductiveTypeNotASort {
        /// The non-`Sort` type that was supplied for the inductive.
        got: ExprId,
    },
    /// A constructor's result head was not the inductive being declared (its
    /// telescope did not end in `I`).
    ConstructorResultMismatch {
        /// The inductive that the constructor should have produced.
        expected: crate::name::NameId,
        /// The constructor whose result was wrong.
        ctor: crate::name::NameId,
    },
    /// A constructor field's type lives in a universe strictly larger than the
    /// inductive family's own result universe. Lean's kernel rejects this
    /// (`check_constructor`: "universe level of the field's type is too big for
    /// the corresponding inductive datatype"); without it an inductive can store
    /// its own universe — `U : Sort 1` with `mk : Sort 1 → U` — which makes
    /// `Sort u` a retract of an inhabitant of `Sort u`, the `Type : Type`
    /// precondition for Girard's paradox. `Prop` (result level zero) is exempt
    /// because it is impredicative.
    ///
    /// Found by `examples/inductive_universe_probe.rs`; see ADR-1495.
    ConstructorFieldUniverseTooBig {
        /// The inductive family being declared.
        inductive: crate::name::NameId,
        /// The constructor containing the offending field.
        ctor: crate::name::NameId,
        /// Zero-based index among the constructor's non-parameter fields.
        field_index: u32,
    },
    /// A constructor field contains the inductive family being declared in the
    /// domain of a function type. Such a negative occurrence violates Lean's
    /// strict-positivity condition and is rejected before the inductive is
    /// provisionally inserted into the environment.
    NonPositiveInductiveOccurrence {
        /// The inductive family whose occurrence is negative.
        inductive: crate::name::NameId,
        /// The constructor containing the offending field.
        ctor: crate::name::NameId,
        /// Zero-based index among the constructor's non-parameter fields.
        field_index: u32,
    },
    /// A constructor field contains the inductive family being declared, but
    /// not as a Lean-valid strictly-positive family application: the head,
    /// universe instantiation, fixed parameters, index arity, or occurrence-
    /// free index condition is invalid.
    InvalidInductiveOccurrence {
        /// The inductive family whose occurrence is invalid.
        inductive: crate::name::NameId,
        /// The constructor containing the offending field.
        ctor: crate::name::NameId,
        /// Zero-based index among the constructor's non-parameter fields.
        field_index: u32,
    },
    /// A constructor field mentioned the inductive type being declared in an
    /// unsupported recursive shape. Valid single-family telescope-tail
    /// recursion is admitted by ADR-0353; this compatibility variant remains
    /// for malformed or future recursive forms outside that boundary.
    /// Non-positive and invalid occurrences have distinct variants above.
    RecursiveInductiveNotSupported {
        /// The inductive whose constructor was recursive.
        inductive: crate::name::NameId,
        /// The recursive constructor.
        ctor: crate::name::NameId,
    },
    /// A constructor field contains an occurrence nested under a foreign head,
    /// or another unsupported shape historically grouped with reflexive/nested
    /// recursion. A positive `Pi` telescope ending directly in the exact family
    /// application is supported; this variant does not reject that shape.
    ReflexiveOrNestedNotSupported {
        /// The inductive whose constructor used a reflexive/nested occurrence.
        inductive: crate::name::NameId,
        /// The offending constructor.
        ctor: crate::name::NameId,
    },
    /// An already admitted container application mentions the expanding
    /// inductive group in its parameters but does not supply the container's
    /// complete parameter prefix.
    NestedInductiveIncompleteApplication {
        /// The existing container family at the application head.
        container: crate::name::NameId,
    },
    /// A nested container parameter contains a loose de Bruijn variable at the
    /// discovery site. Pinned Lean rejects this before expanded admission.
    NestedInductiveLooseParameter {
        /// The existing container family at the application head.
        container: crate::name::NameId,
    },
    /// Previously checked container metadata cannot be reconstructed into the
    /// complete specialized auxiliary group required by nested elimination.
    NestedInductiveMalformedContainer {
        /// The existing container family that could not be copied exactly.
        container: crate::name::NameId,
    },
    /// Deterministic fixed-point expansion exceeded its registered auxiliary-
    /// family bound.
    NestedInductiveExpansionLimit {
        /// Maximum number of auxiliary families permitted in one declaration.
        limit: usize,
    },
    /// A temporary auxiliary family, constructor, or recursor remained in a
    /// restored public type or computation rule.
    NestedInductiveRestorationLeak {
        /// The leaked temporary declaration name.
        name: crate::name::NameId,
    },
    /// Restoration produced a public constructor contract that is not
    /// definitionally equal to the source declaration it is meant to expose.
    NestedInductiveRestorationMismatch {
        /// The public declaration whose restored contract changed.
        name: crate::name::NameId,
    },
    /// A constructor's type used a `Pi` whose result was not an application of
    /// the parent inductive's constant head, or was otherwise malformed for the
    /// parametric scope (e.g. a wrong parameter prefix or an indexed result).
    MalformedConstructorType {
        /// The constructor whose type was malformed.
        ctor: crate::name::NameId,
    },
    /// An inductive type's declared type had **indices**: after opening its
    /// `num_params` parameter binders, a further `Pi` remained before the final
    /// `Sort` (a binder that is an index, not a parameter).
    ///
    /// As of ADR-0036 slice 7, **non-recursive** indexed families (`Eq`, and
    /// finite indexed enums) are supported; this variant is retained for
    /// back-compatibility but is no longer produced by `add_inductive` for a
    /// bare index.
    IndicesNotSupported {
        /// The inductive whose type had indices.
        inductive: crate::name::NameId,
    },
    /// Compatibility error for recursive-indexed fields. ADR-0353 admits valid
    /// single-family occurrences and generates motive applications at the
    /// recursive field's own indices, so `add_inductive` no longer emits this
    /// variant for a valid `Vector`-shaped field. Importer policy or older
    /// callers may still expose the typed code while staged support is widened.
    RecursiveIndexedNotSupported {
        /// The indexed inductive whose constructor was recursive.
        inductive: crate::name::NameId,
        /// The offending recursive constructor.
        ctor: crate::name::NameId,
    },
    /// Constructor checking recorded a recursive field, but recursor
    /// generation could not rederive the same WHNF telescope-tail shape in its
    /// fresh local context. This is an internal checked-metadata mismatch, not
    /// permission to treat the field as non-recursive.
    RecursiveFieldShapeMismatch {
        /// The inductive whose recursive-field metadata disagreed.
        inductive: crate::name::NameId,
        /// The constructor containing the field.
        ctor: crate::name::NameId,
        /// Zero-based index among the constructor's non-parameter fields.
        field_index: u32,
    },
}

/// A single local declaration: an opened binder's name, type, and binder info.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LocalDecl {
    /// The fresh free-variable id this local was opened with.
    pub fvar: u64,
    /// The binder name (for re-abstraction and pretty-printing).
    pub name: crate::name::NameId,
    /// The local's type (already instantiated in the ambient context).
    pub ty: ExprId,
    /// The binder info carried from the originating `Lam`/`Pi`.
    pub info: BinderInfo,
}

/// The cache insertions made while exactly one [`LocalDecl`] was the
/// innermost one open — i.e. the entries recorded between one
/// `LocalContext::push` and its matching `pop`.
///
/// # Why undoing this frame on `pop` is sound
///
/// Every entry recorded here is keyed on an `ExprId` (or a pair of them).
/// The **only** ways a cached `infer`/`def_eq`/`whnf`/`whnf_core` answer can
/// depend on the local declaration stack at all are [`LocalContext::type_of`]
/// (an `FVar`'s type) and [`LocalContext::value_of`] (a let-bound `FVar`'s
/// value) — audited exhaustively: those two, plus the static
/// [`LocalContext::scoped_fvar`] table that `push`/`pop` never touch, are the
/// only local-context reads anywhere in `tc.rs`/`inductive.rs`'s
/// inference/WHNF/def-eq code (`k_like_major` is documented as "the only
/// reduction rule that consults `ctx`", and it does so through `infer_core`'s
/// `FVar` case, i.e. through `type_of`). A given `FVar` id, once minted by
/// [`LocalContext::fresh_fvar`], is never reused within the life of one
/// `LocalContext` (the counter is monotone and
/// [`LocalContext::bump_fresh_above`] only ever raises it), and its
/// `LocalDecl` — hence its `type_of` answer — is fixed for as long as that id
/// remains reachable at all: the few call sites that push the *same* id more
/// than once (the `scoped_fvar` fast path, and shared/mutual-inductive
/// parameters copied into a fresh sibling context) always re-push a
/// byte-identical `LocalDecl` built from the same source expression, never a
/// different one.
///
/// So an entry mentioning `FVar(x)` is valid for exactly as long as `x`'s
/// declaration remains on the stack, i.e. exactly the scope this frame spans.
/// After `x`'s `pop`, any surviving term that could still be validly queried
/// was already re-abstracted (turned back into a bound `Pi`/`Lam`) before the
/// pop happened — nothing legitimately holds an `ExprId` mentioning `x` past
/// this point — so discarding this frame's entries costs at most a recompute
/// if anything ever asks again, never a wrong answer. The lookup-before-insert
/// shape of every one of the four memo functions also rules out an entry EVER
/// being (re)written into two *simultaneously open* frames: once an insert
/// lands, every subsequent lookup for that exact key hits it and returns
/// early, so the same key cannot be journaled again until whichever frame
/// holds it has actually been popped — which is what makes "each frame undoes
/// only its own inserts" well defined instead of a race between frames.
#[derive(Debug, Default)]
struct CacheFrame {
    infer: Vec<ExprId>,
    def_eq: Vec<(ExprId, ExprId)>,
    whnf: Vec<ExprId>,
    whnf_core: Vec<ExprId>,
}

/// A stack of [`LocalDecl`]s for the locals introduced while descending under
/// binders, plus a monotone counter that mints fresh `FVar` ids.
///
/// This stands in for nanoda's de-Bruijn-level machinery: nanoda packs a
/// binder's type into its `Local` node and tracks a `dbj_level_counter`; here
/// the type lives in the stack keyed by a fresh `FVar` id. Push when opening a
/// binder, pop when closing it (LIFO, matching `replace_dbj_level`).
#[derive(Debug, Default)]
pub struct LocalContext {
    decls: Vec<LocalDecl>,
    next_fvar: u64,
    /// Type-inference results valid for exactly the current local declaration
    /// stack. An entry mentioning a since-popped `FVar` is undone via
    /// `cache_journal` rather than the whole table being wiped on every
    /// push/pop — see `CacheFrame` for why that is sound.
    infer_cache: HashMap<ExprId, ExprId>,
    /// Definitional-equality results valid for the current local stack. This is
    /// the local-context analogue of nanoda's equality cache and prevents the
    /// same shared proof/type pair from being compared as an exponential tree.
    /// Undone per-frame on `pop`, like `infer_cache`.
    def_eq_cache: HashMap<(ExprId, ExprId), bool>,
    /// Weak-head normal forms of expressions that mention free variables, and
    /// so may have been computed by consulting this context's declarations.
    ///
    /// This is the context-scoped half of the WHNF cache; the closed half lives
    /// on the kernel (see [`Kernel::whnf_no_unfolding`] for why the split is
    /// where it is). Like `infer_cache` and `def_eq_cache`, it is valid for
    /// exactly the current declaration stack and is undone per-frame on `pop`;
    /// the `u64` pins the environment revision the entries were computed at.
    whnf_cache: (u64, HashMap<ExprId, ExprId>),
    /// **Full-δ** weak-head normal forms of expressions that mention free
    /// variables — the context-scoped half of the `whnf_core` memo, and the
    /// exact analogue of `whnf_cache` one layer up. Undone per-frame on `pop`
    /// with the other three, which is what scopes an entry to the declaration
    /// stack that produced it.
    whnf_core_cache: (u64, HashMap<ExprId, ExprId>),
    /// Definitional values for the subset of locals introduced by `let`.
    let_values: HashMap<u64, ExprId>,
    /// Lambda nodes in a scoped open skeleton whose bodies already refer to the
    /// associated binder as a free variable.
    scoped_fvars: HashMap<ExprId, u64>,
    /// One `CacheFrame` per currently-open binder — `cache_journal.len() ==
    /// decls.len()` is an invariant `push`/`pop` maintain together. Entries
    /// cached at depth 0 (before any binder is open) are never journaled at
    /// all, which is correct: nothing ever pops back below depth 0, so they
    /// should never be undone.
    cache_journal: Vec<CacheFrame>,
    /// Counts every [`LocalContext::type_of`]/[`LocalContext::value_of`] call
    /// that returned `None` — i.e. every observation that some `FVar` is
    /// *currently undeclared*. A memo entry whose computation touched one of
    /// these (see `unbound_probes`) is recording "this fvar is
    /// not yet bound", which a later `push` of exactly that fvar can falsify —
    /// unlike an entry that only ever observed *bound* fvars, whose
    /// declarations are immutable for the rest of their reachable lifetime
    /// (see `CacheFrame`). Such entries are additionally journaled into
    /// `volatile` rather than trusted to survive any push.
    unbound_probes: u64,
    /// Cache entries recorded while `unbound_probes` changed
    /// during their own (uncached) computation — i.e. entries whose answer
    /// depended on some `FVar` currently being undeclared. Drained on every
    /// `push`, regardless of which fvar is being pushed: we cannot cheaply
    /// tell in general which undeclared-fvar observation a tainted entry
    /// depended on, so any push is treated as potentially resolving it. This
    /// is what keeps `pushing_a_local_invalidates_a_memoised_stuck_reduction`
    /// sound under the new per-frame scheme.
    volatile: CacheFrame,
    /// Reference counts of currently-open fvar ids, kept in lockstep with
    /// `decls` by `push`/`pop`, so [`LocalContext::value_of`] can test "is this
    /// id declared at all" in O(1) instead of scanning `decls` — needed only to
    /// classify a let-value miss as "not let-bound" (stable) versus "not
    /// declared at all" (volatile, see `unbound_probes`) without adding an
    /// O(depth) scan to every zeta check of an ordinary bound variable. A
    /// count rather than a set because a scoped fvar id can in principle be
    /// pushed again before an earlier occurrence's matching pop.
    open_fvars: HashMap<u64, u32>,
}

impl LocalContext {
    /// An empty local context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Mint a fresh, never-before-used free-variable id.
    pub fn fresh_fvar(&mut self) -> u64 {
        let id = self.next_fvar;
        self.next_fvar += 1;
        id
    }

    /// Ensure the fresh-id counter is strictly greater than `id`, so that a
    /// subsequently minted fvar cannot collide with an externally-supplied fvar
    /// (e.g. an inductive's shared parameter locals pushed into a fresh context).
    pub fn bump_fresh_above(&mut self, id: u64) {
        if self.next_fvar <= id {
            self.next_fvar = id + 1;
        }
    }

    /// Push a local declaration onto the stack.
    ///
    /// Opens a fresh `CacheFrame` rather than wiping the four memo tables:
    /// see `CacheFrame`'s doc comment for why an unrelated ancestor
    /// computation's memoized entries do not need to be discarded just
    /// because *this* binder opened. Also drains `volatile` —
    /// the entries that recorded some fvar as *undeclared* — since this push
    /// may be exactly what makes one of those observations stale.
    pub fn push(&mut self, decl: LocalDecl) {
        self.cache_journal.push(CacheFrame::default());
        self.drain_volatile();
        *self.open_fvars.entry(decl.fvar).or_insert(0) += 1;
        self.decls.push(decl);
    }

    /// Remove every entry one of the `taint_*_if_unbound_probed` methods
    /// flagged as depending on an undeclared fvar. See the field doc on
    /// `volatile`.
    fn drain_volatile(&mut self) {
        let frame = std::mem::take(&mut self.volatile);
        for key in frame.infer {
            self.infer_cache.remove(&key);
        }
        for key in frame.def_eq {
            self.def_eq_cache.remove(&key);
        }
        for key in frame.whnf {
            self.whnf_cache.1.remove(&key);
        }
        for key in frame.whnf_core {
            self.whnf_core_cache.1.remove(&key);
        }
    }

    /// Snapshot `unbound_probes` before computing an entry
    /// that is about to be memoized. Pair with one of the
    /// `taint_*_if_unbound_probed` methods after the computation.
    fn unbound_probe_mark(&self) -> u64 {
        self.unbound_probes
    }

    /// If `mark` (from [`LocalContext::unbound_probe_mark`]) differs from the
    /// current counter, some `type_of`/`value_of` call made during the
    /// just-finished computation observed an undeclared fvar — journal the
    /// entry just recorded into `volatile` too, in addition to its normal
    /// per-frame journaling, so the next `push` discards it regardless of
    /// which frame it lives in.
    fn taint_infer_if_unbound_probed(&mut self, mark: u64, expression: ExprId) {
        if self.unbound_probes != mark {
            self.volatile.infer.push(expression);
        }
    }

    fn taint_def_eq_if_unbound_probed(&mut self, mark: u64, left: ExprId, right: ExprId) {
        if self.unbound_probes != mark {
            self.volatile.def_eq.push((left, right));
            self.volatile.def_eq.push((right, left));
        }
    }

    fn taint_whnf_if_unbound_probed(&mut self, mark: u64, expression: ExprId) {
        if self.unbound_probes != mark {
            self.volatile.whnf.push(expression);
        }
    }

    fn taint_whnf_core_if_unbound_probed(&mut self, mark: u64, expression: ExprId) {
        if self.unbound_probes != mark {
            self.volatile.whnf_core.push(expression);
        }
    }

    fn push_let(&mut self, decl: LocalDecl, value: ExprId) {
        assert!(
            self.let_values.insert(decl.fvar, value).is_none(),
            "fresh let local must not already have a value"
        );
        self.push(decl);
    }

    /// Pop the most recently pushed local declaration (LIFO).
    ///
    /// Undoes exactly the cache entries recorded in this binder's own
    /// `CacheFrame`, leaving every entry an ancestor scope already built
    /// untouched. `cache_journal` and `decls` are pushed/popped together, so
    /// a frame is only ever discarded when a real declaration was popped with
    /// it (mirrors the `let_values` cleanup above it).
    pub fn pop(&mut self) -> Option<LocalDecl> {
        let popped = self.decls.pop();
        if let Some(decl) = popped {
            self.let_values.remove(&decl.fvar);
            if let std::collections::hash_map::Entry::Occupied(mut entry) =
                self.open_fvars.entry(decl.fvar)
            {
                let count = entry.get_mut();
                *count -= 1;
                if *count == 0 {
                    entry.remove();
                }
            }
            if let Some(frame) = self.cache_journal.pop() {
                for key in frame.infer {
                    self.infer_cache.remove(&key);
                }
                for key in frame.def_eq {
                    self.def_eq_cache.remove(&key);
                }
                for key in frame.whnf {
                    self.whnf_cache.1.remove(&key);
                }
                for key in frame.whnf_core {
                    self.whnf_core_cache.1.remove(&key);
                }
            }
        }
        popped
    }

    /// Look up the type recorded for free variable `id`, if any.
    ///
    /// Bumps `unbound_probes` on a miss: "this fvar is not
    /// currently declared" is itself an observation a memoized answer can
    /// depend on, and unlike a `Some` answer (permanent for the fvar's
    /// reachable lifetime, see `CacheFrame`) a `None` answer can flip to
    /// `Some` on the very next `push`.
    #[must_use]
    pub fn type_of(&mut self, id: u64) -> Option<ExprId> {
        let found = self.decls.iter().rev().find(|d| d.fvar == id).map(|d| d.ty);
        if found.is_none() {
            self.unbound_probes += 1;
        }
        found
    }

    /// See [`LocalContext::type_of`] for why an *undeclared* miss is counted.
    ///
    /// A miss here is ambiguous on its own: `id` may simply be an ordinary
    /// (non-`let`) declared local, which is the overwhelmingly common case
    /// every zeta check hits and is a perfectly stable fact for the fvar's
    /// whole reachable lifetime, not a volatile one. Only a miss where `id`
    /// is not declared **at all** is the same "may flip on the next push"
    /// observation `type_of` counts, so only that case bumps
    /// `unbound_probes` — checked in O(1) via `open_fvars` rather than
    /// re-scanning `decls` on every ordinary bound-variable zeta check.
    fn value_of(&mut self, id: u64) -> Option<ExprId> {
        let found = self.let_values.get(&id).copied();
        if found.is_none() && !self.open_fvars.contains_key(&id) {
            self.unbound_probes += 1;
        }
        found
    }

    fn inferred(&self, expression: ExprId) -> Option<ExprId> {
        self.infer_cache.get(&expression).copied()
    }

    /// The context-scoped WHNF result for `expression`, if one was recorded at
    /// the same environment `revision` and under the current declaration stack.
    fn whnf_result(&mut self, revision: u64, expression: ExprId) -> Option<ExprId> {
        if self.whnf_cache.0 != revision {
            self.whnf_cache.0 = revision;
            self.whnf_cache.1.clear();
            return None;
        }
        self.whnf_cache.1.get(&expression).copied()
    }

    /// The context-scoped half of the full-δ memo. Same shape as
    /// [`LocalContext::whnf_result`]: a revision change makes every entry
    /// unreachable before the first lookup at the new revision.
    fn whnf_core_result(&mut self, revision: u64, expression: ExprId) -> Option<ExprId> {
        if self.whnf_core_cache.0 != revision {
            self.whnf_core_cache.0 = revision;
            self.whnf_core_cache.1.clear();
            return None;
        }
        self.whnf_core_cache.1.get(&expression).copied()
    }

    /// The revision check here is load-bearing rather than defensive; see
    /// [`Kernel::remember_whnf_core`] for the measurement that says so.
    ///
    /// A revision bump's `.clear()` here can make an older frame's journal
    /// entry for `expression` point at nothing; that is harmless (removing an
    /// absent key is a no-op) and not a leak either, because by the time that
    /// older, shallower frame's own `pop` runs, every deeper frame between it
    /// and here has already popped and undone whatever it (re)inserted —
    /// `push`/`pop` are strictly LIFO, so no frame can outlive an ancestor
    /// whose entries it might otherwise clobber.
    fn remember_whnf_core(&mut self, revision: u64, expression: ExprId, normalized: ExprId) {
        if self.whnf_core_cache.0 != revision {
            self.whnf_core_cache.0 = revision;
            self.whnf_core_cache.1.clear();
        }
        self.whnf_core_cache.1.insert(expression, normalized);
        if let Some(frame) = self.cache_journal.last_mut() {
            frame.whnf_core.push(expression);
        }
    }

    /// See [`LocalContext::remember_whnf_core`] for why the revision-bump
    /// interaction with per-frame undo is sound.
    fn remember_whnf(&mut self, revision: u64, expression: ExprId, normalized: ExprId) {
        if self.whnf_cache.0 != revision {
            self.whnf_cache.0 = revision;
            self.whnf_cache.1.clear();
        }
        self.whnf_cache.1.insert(expression, normalized);
        if let Some(frame) = self.cache_journal.last_mut() {
            frame.whnf.push(expression);
        }
    }

    fn remember_inferred(&mut self, expression: ExprId, ty: ExprId) {
        self.infer_cache.insert(expression, ty);
        if let Some(frame) = self.cache_journal.last_mut() {
            frame.infer.push(expression);
        }
    }

    fn def_eq_result(&self, left: ExprId, right: ExprId) -> Option<bool> {
        self.def_eq_cache.get(&(left, right)).copied()
    }

    fn remember_def_eq(&mut self, left: ExprId, right: ExprId, result: bool) {
        self.def_eq_cache.insert((left, right), result);
        self.def_eq_cache.insert((right, left), result);
        if let Some(frame) = self.cache_journal.last_mut() {
            frame.def_eq.push((left, right));
            frame.def_eq.push((right, left));
        }
    }

    fn scoped_fvar(&self, lambda: ExprId) -> Option<u64> {
        self.scoped_fvars.get(&lambda).copied()
    }

    /// Look up the full declaration recorded for free variable `id`, if any.
    #[must_use]
    pub fn decl_of(&self, id: u64) -> Option<LocalDecl> {
        self.decls.iter().rev().find(|d| d.fvar == id).copied()
    }
}

// ---------------------------------------------------------------------------
// WHNF — weak head normal form for the environment-free fragment
// ---------------------------------------------------------------------------

impl Kernel {
    /// Collect the spine of an application `f a1 a2 .. an` into the head `f`
    /// and the argument list `[a1, .., an]` (outermost-first).
    pub(crate) fn unfold_apps(&self, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
        let mut args = Vec::new();
        while let ExprNode::App(f, a) = self.expr_node(e) {
            args.push(*a);
            e = *f;
        }
        args.reverse();
        (e, args)
    }

    /// Re-apply `head` to `args` left-to-right.
    pub(crate) fn foldl_apps(
        &mut self,
        mut head: ExprId,
        args: impl IntoIterator<Item = ExprId>,
    ) -> ExprId {
        for a in args {
            head = self.app(head, a);
        }
        head
    }

    /// Weak head normal form **without** δ-unfolding: beta, zeta (both the
    /// `Let` node and a **let-bound local**, as Lean's `whnf_fvar` does), and
    /// `Sort`-level simplification only. Ported from nanoda's
    /// `whnf_no_unfolding`. A head `Const`/`Sort`/`Pi`, a free variable the
    /// context records no value for, or a `Lam` with no further arguments is
    /// already weak-head-normal here.
    ///
    /// # Memoisation, and why it is split in two
    ///
    /// Reduction may consult `ctx` (K-like reduction reads the *type* of a free
    /// variable), so a WHNF result is in general a function of
    /// `(environment revision, expression, local context)`. The kernel-global
    /// [`Kernel::whnf_cache`] has no context component in its key, and it cannot
    /// gain one usefully: [`LocalContext::new`] restarts its fvar counter at 0,
    /// and [`Kernel::check_declaration`] builds **two** fresh contexts with no
    /// environment change between them, so one kernel-global cache spans local
    /// contexts whose fvar ids collide while denoting different variables.
    ///
    /// The split below makes that key sound by construction rather than by
    /// convention:
    ///
    /// - **Closed expressions** (`has_fvars == false`) go in the kernel-global
    ///   cache. A closed term cannot observe the local context: every reduction
    ///   step (β, ζ, ι, projection, δ) builds only from subterms of the input
    ///   and from environment declarations, and both are closed, so no `FVar`
    ///   can ever appear and no context lookup can ever be reached. The
    ///   `reduction_ctx_reads` tripwire asserted here turns that argument into a
    ///   run-time check: if a future reduction rule reads the context while
    ///   normalizing a closed term, this assertion fires instead of the cache
    ///   silently going wrong.
    /// - **Open expressions** go in a cache owned by the local context itself,
    ///   alongside the `infer_cache` and `def_eq_cache` that already live there
    ///   and are already cleared on every `push`/`pop`. That clearing is what
    ///   scopes an entry to the exact declaration stack that produced it, so an
    ///   answer that depended on a local's type cannot outlive that local.
    fn whnf_no_unfolding(&mut self, e: ExprId, ctx: &mut LocalContext) -> ExprId {
        let revision = self.env.revision();
        if self.has_fvars(e) {
            if let Some(normalized) = ctx.whnf_result(revision, e) {
                return normalized;
            }
            let mark = ctx.unbound_probe_mark();
            let normalized = self.whnf_no_unfolding_uncached(e, ctx);
            ctx.remember_whnf(revision, e, normalized);
            ctx.taint_whnf_if_unbound_probed(mark, e);
            return normalized;
        }
        if self.whnf_cache.0 != revision {
            self.whnf_cache.0 = revision;
            self.whnf_cache.1.clear();
        }
        if let Some(&normalized) = self.whnf_cache.1.get(&e) {
            return normalized;
        }
        let reads_before = self.reduction_ctx_reads;
        let normalized = self.whnf_no_unfolding_uncached(e, ctx);
        assert_eq!(
            self.reduction_ctx_reads, reads_before,
            "reducing a closed expression read the local context; the kernel-global \
             whnf cache key has no context component and would be unsound"
        );
        self.whnf_cache.1.insert(e, normalized);
        normalized
    }

    fn whnf_no_unfolding_uncached(&mut self, e: ExprId, ctx: &mut LocalContext) -> ExprId {
        let mut cursor = e;
        loop {
            let (head, args) = self.unfold_apps(cursor);
            match self.expr_node(head).clone() {
                // Beta: peel as many lambdas as we have arguments, instantiate
                // the consumed args into the body, re-apply any leftover args,
                // then keep reducing.
                ExprNode::Lam(..) if !args.is_empty() => {
                    let mut body = head;
                    let mut n = 0usize;
                    while n < args.len() {
                        match self.expr_node(body) {
                            ExprNode::Lam(_, _, b, _) => {
                                body = *b;
                                n += 1;
                            }
                            _ => break,
                        }
                    }
                    // Instantiate the first `n` args (the innermost binder is
                    // the last consumed, matching nanoda's `inst(.., &args[..n])`).
                    let instd = self.instantiate(body, &args[..n]);
                    cursor = self.foldl_apps(instd, args[n..].iter().copied());
                }
                // Zeta/let: substitute the bound value into the body, re-apply
                // any spine args, keep reducing.
                ExprNode::Let(_, _, val, body) => {
                    let instd = self.instantiate(body, &[val]);
                    cursor = self.foldl_apps(instd, args.iter().copied());
                }
                // ζ over a *local* `let`: a free variable the local context
                // records a value for unfolds to that value. This is Lean's
                // `whnf_fvar` (`type_checker.cpp:346`), reached from the
                // `expr_kind::FVar` arm of its `whnf_core`, and its placement
                // *inside* `whnf_core` is the whole point — every call site
                // gets it, including the `whnf_core(*unfold_definition(...))`
                // inside `lazy_delta_reduction_step`. Doing ζ only at the
                // entry points instead leaves a let-local that becomes a head
                // *during* the delta loop permanently unreduced, which is
                // exactly the `Nat.bitwise._unary` decline: see
                // `local_let_zeta_reduction`.
                ExprNode::FVar(fvar) => match ctx.value_of(fvar) {
                    Some(value) => {
                        // A *hit* is the context changing the reduct, which is
                        // what the closed-expression tripwire in
                        // `whnf_no_unfolding` watches for. A **miss** is not
                        // counted, and the distinction is load-bearing rather
                        // than fussy: reduction of a closed expression can call
                        // inference (K-like reduction infers its major), that
                        // inference opens *its own* binders, and reducing under
                        // them meets ordinary valueless locals. Counting those
                        // made the tripwire fire on two of the first 250 Mathlib
                        // streams — on a reduct that did not depend on the
                        // context at all. A miss returns the term unchanged,
                        // exactly as an empty context would, so it cannot.
                        self.reduction_ctx_reads += 1;
                        cursor = self.foldl_apps(value, args.iter().copied());
                    }
                    None => return cursor,
                },
                // Projection: normalize the projected value; when it becomes a
                // constructor application, select the requested field after
                // the constructor parameters and re-apply any outer spine.
                ExprNode::Proj(..) => match self.reduce_projection(cursor, ctx) {
                    Some(reduced) => cursor = reduced,
                    None => return cursor,
                },
                // ι: a recursor `Const(I.rec, _)` applied to its premises and a
                // constructor-headed major reduces to the matching minor applied
                // to the constructor's fields (ADR-0036, slice 4).
                ExprNode::Const(..) => {
                    if let Some(reduced) = self.reduce_quotient(cursor, ctx) {
                        cursor = reduced;
                    } else if let Some(reduced) = self.reduce_rec(cursor, ctx) {
                        cursor = reduced;
                    } else if let Some(reduced) = self.reduce_nat_succ(cursor, ctx) {
                        cursor = reduced;
                    } else {
                        // The **binary** `Nat` acceleration is deliberately not
                        // here. Lean's `reduce_nat` is called from `whnf`
                        // (`type_checker.cpp:670`) and from
                        // `lazy_delta_reduction` (`:978`), never from
                        // `whnf_core` — and this function *is* Lean's
                        // `whnf_core`. See `Kernel::whnf_core` and
                        // `Kernel::lazy_delta_step` for the two sites, and
                        // ADR-0536 for why the placement is a decision rather
                        // than a refactor.
                        //
                        // `reduce_nat_succ` stays because it is guarded by an
                        // interned-name comparison against `Nat.succ` before it
                        // reduces anything, so a failing probe costs a compare;
                        // the binary rule's failing probe δ-normalises two
                        // arguments.
                        return cursor;
                    }
                }
                // A bare `Sort` is normal; simplify its level for canonicity.
                ExprNode::Sort(level) if args.is_empty() => {
                    let level = self.simplify(level);
                    return self.sort(level);
                }
                // All other heads are already weak-head-normal here: Sort
                // (applied — ill-typed but inert), Pi, BVar (loose — inert),
                // Lit, and Lam with no args. A *valueless* FVar returns from
                // its own arm above.
                _ => return cursor,
            }
        }
    }

    /// Try one constructor-projection reduction step.
    ///
    /// This mirrors Lean's `reduce_proj_core`: normalize the projected value,
    /// require a constructor head, obtain the constructor's checked parameter
    /// count from its parent inductive, and select argument
    /// `num_params + field_index`. Reduction intentionally follows the actual
    /// constructor and does not re-check the structure name stored in the
    /// projection node; projection inference owns that well-typedness check,
    /// matching Lean's separation between reduction and inference.
    fn reduce_projection(&mut self, expression: ExprId, ctx: &mut LocalContext) -> Option<ExprId> {
        let (head, trailing) = self.unfold_apps(expression);
        let ExprNode::Proj(_, field_index, structure) = self.expr_node(head).clone() else {
            return None;
        };

        let structure = self.whnf_core(structure, ctx);
        // Lean's `reduce_proj_core`: a projected String literal becomes its
        // `String.ofList` expansion, normalized to the structure constructor,
        // before ordinary field selection.
        let structure = self.expand_string_literal_major(structure, ctx);
        let (ctor_head, ctor_args) = self.unfold_apps(structure);
        let ExprNode::Const(ctor_name, _) = self.expr_node(ctor_head) else {
            return None;
        };
        let inductive = match self.env.get(*ctor_name) {
            Some(Declaration::Constructor { inductive, .. }) => *inductive,
            _ => return None,
        };
        let num_params = match self.env.get(inductive) {
            Some(Declaration::Inductive { num_params, .. }) => usize::from(*num_params),
            _ => return None,
        };
        let selected_index = num_params.checked_add(usize::try_from(field_index).ok()?)?;
        let selected = ctor_args.get(selected_index).copied()?;
        Some(self.foldl_apps(selected, trailing))
    }

    /// Weak head normal form for the in-scope fragment.
    ///
    /// Performs **beta** (`App(Lam, a)` → instantiate the lambda body),
    /// **zeta/let** (`Let` → instantiate the value into the body), and **δ**
    /// (unfold a `Definition`/`Theorem` `Const` head to its value with
    /// universe parameters instantiated) reduction, iterating to a
    /// weak-head-normal term. `Sort` levels are simplified to a canonical form.
    /// **Eta** is *not* performed here — it lives in [`Kernel::def_eq`],
    /// matching nanoda.
    ///
    /// `Opaque` and `Axiom` `Const` heads do **not** δ-unfold (matching
    /// nanoda's `get_declar_val`). Inductive ι and constructor-projection
    /// reduction are included; quotient reduction remains deferred.
    ///
    /// Reduction happens in the **empty** local context, so rules that consult
    /// it cannot fire on an open term here: K-like reduction (which needs a
    /// free variable's *type*) and ζ over a local `let` (which needs its
    /// *value*) both no-op, so a let-bound variable looks irreducible. That is
    /// a restriction, never a widening: fewer reductions means fewer terms
    /// identified. It is also the reason a diagnostic that reduces an error's
    /// two `ExprId`s here can stop on a bare `_fvar` the checker would have
    /// reduced — see `wf_recursion_decline_probe`. Callers that are already
    /// under binders should use `Kernel::whnf_core` with their own context.
    /// (That link is deliberately plain text: `whnf_core` is private, and an
    /// intra-doc link to it makes `cargo doc` warn — which CI turns into an
    /// error via `RUSTDOCFLAGS="-D warnings"`.)
    ///
    /// # Panics
    ///
    /// Does not panic on well-formed input.
    #[must_use]
    pub fn whnf(&mut self, e: ExprId) -> ExprId {
        let mut ctx = LocalContext::new();
        self.whnf_core(e, &mut ctx)
    }

    /// Reduce beta, zeta, iota, and projection redexes without delta-unfolding
    /// any named declaration. This is useful to inspect one explicitly
    /// unfolded definition before deciding whether another delta step is
    /// appropriate; unlike [`Kernel::whnf`], it cannot run through the next
    /// recursive constant and expose its implementation recursor.
    #[must_use]
    pub fn whnf_without_delta(&mut self, e: ExprId) -> ExprId {
        let mut ctx = LocalContext::new();
        self.whnf_no_unfolding(e, &mut ctx)
    }

    /// Delta-unfold exactly the outer applied definition once, reapplying its
    /// argument spine but performing no further reduction. Axioms, opaque
    /// declarations, constructors, and expressions without a definition head
    /// return `None`.
    #[must_use]
    pub fn unfold_definition_once(&mut self, e: ExprId) -> Option<ExprId> {
        self.unfold_def(e)
    }

    /// The **pre-fix** reduction entry point, kept so that the unsoundness it
    /// carries can be *run* rather than argued about.
    ///
    /// This is `whnf_core` as it stood before the cache was split: one
    /// kernel-global memo table keyed on `(environment revision, ExprId)` for
    /// every expression, open or closed. With a context-consulting reduction
    /// rule in the loop (K-like reduction) that key is wrong, and
    /// `tc_tests::whnf_cache_key_collision_is_constructible` uses this function
    /// to exhibit the wrong answer directly.
    ///
    /// `#[cfg(test)]`, and deliberately so: nothing that ships may call it.
    #[cfg(test)]
    pub(crate) fn whnf_core_context_free_cached(
        &mut self,
        e: ExprId,
        ctx: &mut LocalContext,
    ) -> ExprId {
        let mut cursor = e;
        loop {
            let revision = self.env.revision();
            if self.whnf_cache.0 != revision {
                self.whnf_cache.0 = revision;
                self.whnf_cache.1.clear();
            }
            let whnfd = if let Some(&normalized) = self.whnf_cache.1.get(&cursor) {
                normalized
            } else {
                let normalized = self.whnf_no_unfolding_uncached(cursor, ctx);
                self.whnf_cache.1.insert(cursor, normalized);
                normalized
            };
            match self.unfold_def(whnfd) {
                Some(next) => cursor = next,
                None => return whnfd,
            }
        }
    }

    /// [`Kernel::whnf`] in an existing local context.
    ///
    /// The context is what lets reduction see a free variable's *type*, which
    /// K-like reduction needs. Everything else about the two entry points is
    /// identical.
    ///
    /// # The memo
    ///
    /// The δ loop is memoised on `(environment revision, expression)` with the
    /// same closed/open split, and for the same reason, as the δ-free memo in
    /// [`Kernel::whnf_no_unfolding`] — read that first; the argument is not
    /// repeated here. This is a **memo and nothing else**: the loop is a
    /// deterministic function of the key, so a hit returns exactly what the walk
    /// would have returned, and the set of terms the kernel identifies is
    /// unchanged. Nothing here decides *whether* a reduction fires.
    ///
    /// Per-step memoisation is not enough, which is why this layer exists at
    /// all. `whnf_no_unfolding` already caches one δ-free step, but a repeated
    /// `whnf_core` still re-walks the entire δ chain a probe at a time, and
    /// every link that δ-unfolds mints a **fresh** expression that no cache has
    /// ever seen. Measured on `build_creal_prelude` (2026-08-20, this host):
    /// 33.0 s without this memo, 13.0 s with it.
    ///
    /// The pinned reference carries both layers and we carried only one:
    /// `type_checker.h:31-32` declares `m_whnf_core` *and* `m_whnf`, populated
    /// at `type_checker.cpp:491/548` and `755/763-772` respectively. Our
    /// `whnf_no_unfolding` is Lean's `whnf_core` and this is Lean's `whnf`, so
    /// the missing cache was the second of that pair.
    ///
    /// The traffic that makes it matter is the literal-`Nat` acceleration.
    /// [`Kernel::reduce_nat_binop`] runs `whnf_core` on **both** arguments of
    /// every `Nat.add`/`Nat.mul`/`Nat.div`/`Nat.mod`/`Nat.gcd`/`Nat.beq`
    /// application it meets — from *inside* the δ-free normaliser, so the δ
    /// work that lazy-delta exists to avoid is done eagerly and speculatively.
    /// In that build it fired 1.19 M times and produced a literal 575 times.
    /// (It fires at all only since `502184d3f`: `Kernel::build_nat_binop_table`
    /// requires `Bool`'s constructors in official Lean order, so while the
    /// native `Bool` was `[true, false]` the whole table was `None` and every
    /// probe returned immediately. Aligning `Bool` switched the acceleration on
    /// and the prelude build went 8.7 s → 33.0 s.)
    pub(crate) fn whnf_core(&mut self, e: ExprId, ctx: &mut LocalContext) -> ExprId {
        let revision = self.env.revision();
        if let Some(normalized) = self.recall_whnf_core(revision, e, ctx) {
            return normalized;
        }
        let reads_before = self.reduction_ctx_reads;
        let entry_closed = !self.has_fvars(e);
        let mark = ctx.unbound_probe_mark();

        // Every link of the δ chain has the SAME full-δ normal form as `e`:
        // `whnf_core` is deterministic and the walk from a link is the tail of
        // the walk from `e`. So the whole chain is memoised, not just its head.
        // That is where the win is: each δ step *mints a fresh expression*, and
        // those intermediates are exactly the ones nothing else ever caches.
        let mut chain: Vec<(ExprId, u64)> = Vec::new();
        let mut cursor = e;
        let normalized = loop {
            if cursor != e
                && let Some(normalized) = self.recall_whnf_core(revision, cursor, ctx)
            {
                break normalized;
            }
            chain.push((cursor, self.reduction_ctx_reads));
            let whnfd = self.whnf_no_unfolding(cursor, ctx);
            // Lean's `whnf`: `reduce_nat` is tried on the `whnf_core` result,
            // **before** δ (`type_checker.cpp:670`), so a literal `Nat`
            // operation is evaluated instead of unfolding its recursive
            // definition. The `has_fvars` guard is Lean's own
            // (`type_checker.cpp:978`) but Lean applies it only at the
            // lazy-delta site; carrying it here too is strictly more
            // conservative than Lean and is the decision recorded in ADR-0536.
            //
            // The head of a two-argument `Nat` application is a closed `Const`,
            // so `!has_fvars(whnfd)` is exactly "neither argument mentions a
            // free variable" — the condition under which the two `whnf_core`
            // calls inside the rule can still land on literals.
            if !self.has_fvars(whnfd)
                && let Some(reduced) = self.reduce_nat_binop(whnfd, ctx)
            {
                cursor = reduced;
                continue;
            }
            match self.unfold_def(whnfd) {
                Some(next) => cursor = next,
                None => break whnfd,
            }
        };

        // Every link is routed into the split memo by *its own* closedness, so
        // the tripwire has to be per-link too. `entry_closed` alone does not
        // cover it: an OPEN entry can δ-unfold to a CLOSED link, which is then
        // written to the kernel-global half — the half whose key has no context
        // component at all. That is not hypothetical and not rare enough to
        // argue away: measured 2026-08-20, one `build_creal_prelude` routes 6
        // such links, and the entry-gated form of this assertion looked at none
        // of them.
        //
        // `reads_at_link` is snapshotted when the link is pushed, before
        // anything reduces it, so the comparison is exactly "did the walk from
        // HERE onward consult the context".
        //
        // Stated plainly, because a guard that cannot fail is worse than none:
        // **neutering this assertion kills no test**, and no test can be written
        // that makes it fire, because "a closed term's reduction cannot reach a
        // context lookup" is a theorem about `has_fvars`, not a condition some
        // input violates. Its sibling on `entry_closed` is the same. What it
        // buys is that the theorem is re-checked at runtime, in release, on
        // every link actually routed — and what keeps it from being decoration
        // is `an_open_entry_delta_unfolds_to_a_closed_link_stored_context_free`,
        // which fails if the chain stops producing the links this looks at.
        for &(link, reads_at_link) in &chain {
            assert!(
                self.has_fvars(link) || self.reduction_ctx_reads == reads_at_link,
                "δ-normalizing a closed expression read the local context; the \
                 kernel-global whnf_core cache key has no context component and \
                 would be unsound"
            );
        }
        debug_assert!(
            !entry_closed || self.reduction_ctx_reads == reads_before,
            "the per-link tripwire must subsume the entry-closed case"
        );
        // One shared mark for the whole chain: taint is conservative over
        // *which* link's reduction touched an undeclared fvar, since any of
        // them can (`k_like_major`/`structure_eta_major`/the zeta arm all
        // read `ctx`, and a single walk can pass through several links).
        let tainted = ctx.unbound_probe_mark() != mark;
        for (link, _) in chain {
            self.remember_whnf_core(revision, link, normalized, ctx);
            if tainted {
                ctx.taint_whnf_core_if_unbound_probed(mark, link);
            }
        }
        normalized
    }

    /// The memoised full-δ normal form of `e`, if one is recorded.
    ///
    /// Routed by `e`'s own closedness, exactly as [`Kernel::whnf_no_unfolding`]
    /// routes its δ-free memo and for the same reason: the kernel-global key
    /// has no local-context component, so only a closed expression — one whose
    /// reduction provably cannot consult the context — may live there.
    fn recall_whnf_core(
        &mut self,
        revision: u64,
        e: ExprId,
        ctx: &mut LocalContext,
    ) -> Option<ExprId> {
        if self.has_fvars(e) {
            return ctx.whnf_core_result(revision, e);
        }
        if self.whnf_core_cache.0 != revision {
            self.whnf_core_cache.0 = revision;
            self.whnf_core_cache.1.clear();
            return None;
        }
        self.whnf_core_cache.1.get(&e).copied()
    }

    /// Record `normalized` as the full-δ normal form of `e`, in whichever half
    /// of the split memo `e`'s closedness selects.
    ///
    /// The revision check on the way *in* is not redundant with the one on the
    /// way out, and I had it the other way round until an assertion said
    /// otherwise. The argument for dropping it was that every link is recalled
    /// at the same revision first, so the recall's stamp always precedes the
    /// write. Replacing the branch with `debug_assert_eq!` and running the unit
    /// sweep killed six tests: a **fresh** `LocalContext` whose first
    /// `whnf_core` entry is *closed* is never stamped by a recall at all (the
    /// recall goes to the kernel-global half), so the first open link written
    /// into it arrives at an unstamped cache. It is this branch that stamps it.
    fn remember_whnf_core(
        &mut self,
        revision: u64,
        e: ExprId,
        normalized: ExprId,
        ctx: &mut LocalContext,
    ) {
        if self.has_fvars(e) {
            ctx.remember_whnf_core(revision, e, normalized);
            return;
        }
        if self.whnf_core_cache.0 != revision {
            self.whnf_core_cache.0 = revision;
            self.whnf_core_cache.1.clear();
        }
        self.whnf_core_cache.1.insert(e, normalized);
    }
}

// ---------------------------------------------------------------------------
// δ-reduction and the declaration/environment layer (ADR-0036, slice 3)
// ---------------------------------------------------------------------------

impl Kernel {
    /// Build a `Param(name) ↦ level` substitution pairing each universe
    /// parameter with its instantiating argument positionally. Callers must
    /// have already checked `uparams.len() == level_args.len()`.
    fn level_subst(uparams: &[NameId], level_args: &[LevelId]) -> Vec<(NameId, LevelId)> {
        uparams
            .iter()
            .copied()
            .zip(level_args.iter().copied())
            .collect()
    }

    /// Try to **δ-unfold** the base `Const` head of `e`: if `e` is
    /// `Const(name, levels) a1 .. an` (or a bare `Const`) whose declaration has
    /// an unfoldable value (`Definition`/`Theorem`) and whose universe-argument
    /// count matches, substitute the universe args into the value and re-apply
    /// the spine. Returns `None` for non-`Const` heads, unknown constants,
    /// `Axiom`/`Opaque` (no unfolding), or universe arity mismatch. Ported from
    /// nanoda's `unfold_def`.
    fn unfold_def(&mut self, e: ExprId) -> Option<ExprId> {
        let (fun, args) = self.unfold_apps(e);
        let ExprNode::Const(name, levels) = self.expr_node(fun).clone() else {
            return None;
        };
        let decl = self.env.get(name)?;
        let value = decl.delta_value()?;
        let uparams = decl.uparams().to_vec();
        if uparams.len() != levels.len() {
            return None;
        }
        let subst = Self::level_subst(&uparams, &levels);
        let instantiated = self.substitute_expr_levels(value, &subst);
        Some(self.foldl_apps(instantiated, args))
    }

    /// For an expression whose head is a `Const` naming an unfoldable
    /// declaration, return that declaration's name and reducibility hint
    /// (the only data lazy-delta needs). `Theorem` reports
    /// [`ReducibilityHint::Opaque`]; `Axiom`/`Opaque`/unknown/non-`Const`
    /// return `None`. Ported from nanoda's `get_applied_def`.
    fn get_applied_def(&self, e: ExprId) -> Option<(NameId, ReducibilityHint)> {
        let (head, _) = self.unfold_apps(e);
        let ExprNode::Const(name, _) = self.expr_node(head) else {
            return None;
        };
        let name = *name;
        let decl = self.env.get(name)?;
        decl.delta_hint().map(|hint| (name, hint))
    }

    /// δ-unfold a single applied definition and re-normalize cheaply
    /// (no further δ). Ported from nanoda's `delta`.
    ///
    /// # Panics
    ///
    /// Panics if `e` is not an applied unfoldable definition (callers in
    /// lazy-delta have already established this via [`Kernel::get_applied_def`],
    /// matching nanoda's `delta`).
    fn delta(&mut self, e: ExprId, ctx: &mut LocalContext) -> ExprId {
        let unfolded = self
            .unfold_def(e)
            .expect("delta called on a non-unfoldable expression");
        self.whnf_no_unfolding(unfolded, ctx)
    }
}

// ---------------------------------------------------------------------------
// The trusted declaration-admission gate
// ---------------------------------------------------------------------------

impl Kernel {
    /// Type-check and admit a [`Declaration`] into the global environment —
    /// the **trusted kernel gate**.
    ///
    /// Admission requires (matching nanoda's `check_declar` for the
    /// non-inductive kinds):
    ///
    /// 1. no declaration with the same name already exists;
    /// 2. the declared type infers (and WHNFs) to a `Sort` (it is a type);
    /// 3. for `Definition`/`Theorem`/`Opaque`, the value's inferred type is
    ///    definitionally equal to the declared type.
    ///
    /// Inference/def-eq run under the declaration's universe parameters as
    /// `Param`s, so universe-polymorphic declarations type-check abstractly.
    ///
    /// On success the declaration is inserted and `Ok(())` returned; on any
    /// failure the environment is left unchanged and a [`KernelError`] is
    /// returned. A wrong check here would admit a false theorem, so the checks
    /// are genuine — never skipped.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError::DeclarationExists`] for a duplicate name,
    /// [`KernelError::DuplicateUniverseParam`] if the declaration binds the same
    /// universe parameter twice,
    /// [`KernelError::UndeclaredUniverseParam`] if the type or value mentions a
    /// universe parameter the declaration does not bind,
    /// [`KernelError::DeclarationTypeNotASort`] if the type is not a type,
    /// [`KernelError::DeclarationValueMismatch`] if a value's type does not
    /// match the declared type, or any [`KernelError`] surfaced while inferring
    /// the type or value (e.g. [`KernelError::UnknownConst`] for a dangling
    /// reference).
    pub fn add_declaration(&mut self, decl: Declaration) -> Result<(), KernelError> {
        let name = decl.name();
        if matches!(&decl, Declaration::Quotient { .. }) {
            return Err(KernelError::QuotientPackageRequired { name });
        }
        if self.env.contains(name) {
            return Err(KernelError::DeclarationExists { name });
        }

        self.check_declaration(&decl)?;
        self.env.insert_unchecked(decl);
        Ok(())
    }

    /// Check one declaration's ordinary type/value contract without inserting
    /// it. Privileged package gates use this after their own shape validation.
    pub(crate) fn check_declaration(&mut self, decl: &Declaration) -> Result<(), KernelError> {
        // (1a) The binding list must not repeat a name. This is not hygiene
        // either: `Const(c, us)` substitutes positionally, so a repeated
        // parameter has two candidate substitutions at every use and the
        // declaration denotes nothing definite. Lean refuses it; this kernel
        // admitted it until the public conformance corpus's `tut06_bad01` case
        // measured the divergence (ADR-1663, `docs/plan/lean-divergences.md` D2).
        //
        // Linear in a list that is one or two long in practice, so the quadratic
        // scan is cheaper than allocating a set on every admission.
        let uparams = decl.uparams();
        for (index, &param) in uparams.iter().enumerate() {
            if uparams[..index].contains(&param) {
                return Err(KernelError::DuplicateUniverseParam {
                    declaration: decl.name(),
                    param,
                });
            }
        }

        // (1b) Universe closure: every `Param` the type or the value mentions
        // must be one this declaration binds.
        //
        // This has to come first and has to be its own check, because the two
        // that follow are *relative*: inference and def-eq treat an unbound
        // `Param` exactly like a bound one, so they hold just as well with a
        // free `u` on both sides. Nothing else in the kernel ever compares the
        // parameters occurring in a term against the parameters the
        // declaration declares, which left the binding list decorative.
        for expr in [Some(decl.ty()), decl.value()].into_iter().flatten() {
            if let Some(param) = self.undeclared_universe_param(expr, decl.uparams()) {
                return Err(KernelError::UndeclaredUniverseParam {
                    declaration: decl.name(),
                    param,
                });
            }
        }

        // (2) The declared type must itself be a type (infer to a `Sort`).
        let ty = decl.ty();
        let mut ctx = LocalContext::new();
        let ty_ty = self.infer_core(ty, &mut ctx)?;
        let ty_ty = self.whnf(ty_ty);
        if !matches!(self.expr_node(ty_ty), ExprNode::Sort(_)) {
            return Err(KernelError::DeclarationTypeNotASort { got: ty_ty });
        }

        // (3) The value (if any) must check against the declared type.
        if let Some(value) = decl.value() {
            let mut ctx = LocalContext::new();
            let value_ty = self.infer_core(value, &mut ctx)?;
            if !self.def_eq_core(value_ty, ty, &mut ctx) {
                return Err(KernelError::DeclarationValueMismatch {
                    declared: ty,
                    inferred: value_ty,
                });
            }
        }

        Ok(())
    }

    /// The first universe parameter `e` mentions that is not in `bound`, if any.
    ///
    /// Not `pub(crate)`, for two reasons that are the same reason. The inductive
    /// gate does its own type checking and never routes through
    /// `Kernel::check_declaration` (private, hence unlinked), so it has to run
    /// this check itself or
    /// inductives are the one declaration kind whose universe parameters stay
    /// decorative. And a *recursor* record on an import stream is checked by
    /// comparison against the recursor this kernel generated, never admitted —
    /// so the kernel never sees the exported binding list at all, and the
    /// importer needs this walk to check it. Both callers are checking a
    /// binding list against the parameters a term actually mentions, which is
    /// the one question nothing else in the kernel asks.
    ///
    /// Expressions are interned DAGs, so the walk memoizes on `ExprId`; without
    /// that a shared subterm is revisited once per reference and a large
    /// prelude declaration is exponential.
    #[must_use]
    pub fn undeclared_universe_param(&self, e: ExprId, bound: &[NameId]) -> Option<NameId> {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![e];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            match self.expr_node(current) {
                ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Lit(_) => {}
                ExprNode::Sort(level) => {
                    if let Some(stray) = self.undeclared_level_param(*level, bound) {
                        return Some(stray);
                    }
                }
                ExprNode::Const(_, levels) => {
                    for &level in levels {
                        if let Some(stray) = self.undeclared_level_param(level, bound) {
                            return Some(stray);
                        }
                    }
                }
                ExprNode::Proj(_, _, structure) => stack.push(*structure),
                ExprNode::App(function, argument) => {
                    stack.push(*function);
                    stack.push(*argument);
                }
                ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                    stack.push(*ty);
                    stack.push(*body);
                }
                ExprNode::Let(_, ty, value, body) => {
                    stack.push(*ty);
                    stack.push(*value);
                    stack.push(*body);
                }
            }
        }
        None
    }

    /// The first universe parameter in `level` that is not in `bound`, if any.
    fn undeclared_level_param(&self, level: LevelId, bound: &[NameId]) -> Option<NameId> {
        let mut stack = vec![level];
        while let Some(current) = stack.pop() {
            match self.level_node(current) {
                LevelNode::Zero => {}
                LevelNode::Succ(inner) => stack.push(*inner),
                LevelNode::Max(left, right) | LevelNode::IMax(left, right) => {
                    stack.push(*left);
                    stack.push(*right);
                }
                LevelNode::Param(name) => {
                    if !bound.contains(name) {
                        return Some(*name);
                    }
                }
            }
        }
        None
    }
}

// ---------------------------------------------------------------------------
// Definitional equality
// ---------------------------------------------------------------------------

impl Kernel {
    /// `Sort l ~ Sort r` iff the levels are antisymmetrically equivalent.
    fn def_eq_sort(&mut self, x: ExprId, y: ExprId) -> Option<bool> {
        match (self.expr_node(x).clone(), self.expr_node(y).clone()) {
            (ExprNode::Sort(l), ExprNode::Sort(r)) => Some(self.level_is_equiv(l, r)),
            _ => None,
        }
    }

    /// Cheap structural pre-check before any reduction (nanoda's
    /// `def_eq_quick_check`, minus the union-find cache): identity, `Sort`
    /// level-equiv, and `Pi`/`Lam` congruence.
    fn def_eq_quick(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> Option<bool> {
        if x == y {
            return Some(true);
        }
        if let Some(r) = self.def_eq_sort(x, y) {
            return Some(r);
        }
        if let Some(r) = self.def_eq_binder(x, y, ctx) {
            return Some(r);
        }
        if let (ExprNode::Lit(left), ExprNode::Lit(right)) = (self.expr_node(x), self.expr_node(y))
        {
            return Some(left == right);
        }
        None
    }

    /// Congruence for matching binders (`Pi`/`Pi` or `Lam`/`Lam`): the domains
    /// must be def-eq, and the bodies must be def-eq under a fresh shared
    /// `FVar`. Ported from nanoda's `def_eq_binder_aux` (single-binder form;
    /// the multi-binder loop is an optimization, not a semantic change).
    fn def_eq_binder(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> Option<bool> {
        let ((ExprNode::Pi(name, t1, body1, info), ExprNode::Pi(_, t2, body2, _))
        | (ExprNode::Lam(name, t1, body1, info), ExprNode::Lam(_, t2, body2, _))) =
            (self.expr_node(x).clone(), self.expr_node(y).clone())
        else {
            return None;
        };
        if !self.def_eq_core(t1, t2, ctx) {
            return Some(false);
        }
        // Open both bodies under one shared fresh fvar of type `t1`.
        let fvar = ctx.fresh_fvar();
        let fv = self.fvar(fvar);
        ctx.push(LocalDecl {
            fvar,
            name,
            ty: t1,
            info,
        });
        let b1 = self.instantiate(body1, &[fv]);
        let b2 = self.instantiate(body2, &[fv]);
        let r = self.def_eq_core(b1, b2, ctx);
        ctx.pop();
        Some(r)
    }

    /// Spine congruence for applications (nanoda's `def_eq_app`): equal-length
    /// argument lists that are pairwise def-eq, with def-eq heads.
    fn def_eq_app(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        let (f1, args1) = self.unfold_apps(x);
        let (f2, args2) = self.unfold_apps(y);
        if args1.is_empty() || args2.is_empty() || args1.len() != args2.len() {
            return false;
        }
        if !args1
            .iter()
            .zip(args2.iter())
            .all(|(&a, &b)| self.def_eq_core(a, b, ctx))
        {
            return false;
        }
        self.def_eq_core(f1, f2, ctx)
    }

    /// Two `FVar`s are def-eq iff they share the same id (nanoda's
    /// `def_eq_local`; the recorded types are equal by construction since a
    /// fresh fvar is shared across both sides).
    fn def_eq_fvar(&self, x: ExprId, y: ExprId) -> bool {
        matches!(
            (self.expr_node(x), self.expr_node(y)),
            (ExprNode::FVar(a), ExprNode::FVar(b)) if a == b
        )
    }

    /// Two `Const`s are def-eq iff they name the same declaration with
    /// antisymmetrically-equivalent universe arguments (nanoda's
    /// `def_eq_const`).
    fn def_eq_const(&mut self, x: ExprId, y: ExprId) -> bool {
        let (ExprNode::Const(nx, lx), ExprNode::Const(ny, ly)) =
            (self.expr_node(x).clone(), self.expr_node(y).clone())
        else {
            return false;
        };
        if nx != ny || lx.len() != ly.len() {
            return false;
        }
        lx.iter()
            .zip(ly.iter())
            .all(|(&a, &b)| self.level_is_equiv(a, b))
    }

    /// Congruence for two **stuck** projections (Lean's `is_def_eq_core`
    /// `is_proj`/`is_proj` case, feeding `lazy_delta_proj_reduction`):
    /// `a.i ≡ b.i` when `a ≡ b`.
    ///
    /// Why this is needed at all. [`Kernel::reduce_projection`] already fires
    /// whenever the projected value WHNFs to a constructor application, so the
    /// only projections that survive to here are stuck on a neutral value —
    /// canonically a recursor applied to a variable. Lean's compiler emits
    /// exactly that shape for every structurally recursive function: `Nat.add`
    /// is `Nat.brecOn`, `Nat.brecOn` is `(Nat.brecOn.go … t F).1`, and with `t`
    /// a variable the projection cannot reduce on either side. Without this rule
    /// the two sides are compared only by [`Kernel::def_eq_app`], which sees two
    /// bare `Proj` nodes with empty spines and answers `false` — so
    /// `n + succ m ≡ succ (n + m)` was **not** definitional here and every
    /// `rfl`-proved equation of a `brecOn`-compiled function was rejected.
    ///
    /// Why it is sound. This is plain congruence: `Proj` is a term former, and
    /// substituting definitionally equal subterms into a term former yields
    /// definitionally equal terms. It cannot identify two terms that are not
    /// already equal, and it cannot make a stuck term reduce. The **field index
    /// must match** — that is the entire discriminating content of the rule, and
    /// dropping it would identify distinct fields of one structure, so the index
    /// comparison is what the negative tests pin.
    ///
    /// The structure *name* recorded in the node is deliberately **not**
    /// compared, matching Lean (`proj_idx(t_n) == proj_idx(s_n)` only). It is
    /// not needed: `def_eq` runs on terms that have already been inferred, so
    /// both projections are well-typed, `a ≡ b` forces their types to be def-eq,
    /// and an inductive type's head does not reduce — hence the two nodes name
    /// the same structure whenever they agree here. Projection *inference* owns
    /// the name check, exactly as [`Kernel::reduce_projection`] documents for
    /// reduction.
    fn def_eq_proj(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        let (ExprNode::Proj(_, x_field, x_structure), ExprNode::Proj(_, y_field, y_structure)) =
            (self.expr_node(x).clone(), self.expr_node(y).clone())
        else {
            return false;
        };
        x_field == y_field && self.def_eq_core(x_structure, y_structure, ctx)
    }

    /// Eta-expansion (nanoda's `try_eta_expansion`): if one side is a `Lam` and
    /// the other's type WHNFs to a `Pi`, expand the non-lambda `f` into
    /// `fun (x : dom) => f x` (with a lifted `f` and a `BVar 0` argument) and
    /// re-check.
    fn try_eta_expansion(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        self.try_eta_expansion_aux(x, y, ctx) || self.try_eta_expansion_aux(y, x, ctx)
    }

    fn try_eta_expansion_aux(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        if !matches!(self.expr_node(x), ExprNode::Lam(..)) {
            return false;
        }
        let Ok(y_ty) = self.infer_core(y, ctx) else {
            return false;
        };
        let y_ty = self.whnf_core(y_ty, ctx);
        let ExprNode::Pi(name, dom, _, info) = self.expr_node(y_ty).clone() else {
            return false;
        };
        // Build `fun (x : dom) => y x` where the bound var is `BVar 0`. `y`
        // moves under one binder, so its loose bvars lift by 1.
        let v0 = self.bvar(0);
        let y_lifted = self.lift_loose_bvars(y, 0, 1);
        let new_body = self.app(y_lifted, v0);
        let new_lam = self.lam(name, dom, new_body, info);
        self.def_eq_core(x, new_lam, ctx)
    }

    /// Structure eta (Lean's `try_eta_struct`): recognize one side as an
    /// exactly saturated constructor of a non-recursive, non-indexed,
    /// one-constructor inductive, require both sides to have definitionally
    /// equal types, and compare each constructor field with the corresponding
    /// projection from the other side.
    fn try_eta_structure(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        self.try_eta_structure_aux(x, y, ctx) || self.try_eta_structure_aux(y, x, ctx)
    }

    fn try_eta_structure_aux(
        &mut self,
        structure: ExprId,
        constructor_app: ExprId,
        ctx: &mut LocalContext,
    ) -> bool {
        let (head, args) = self.unfold_apps(constructor_app);
        let ExprNode::Const(ctor_name, _) = self.expr_node(head) else {
            return false;
        };
        let (inductive, num_fields) = match self.env.get(*ctor_name) {
            Some(Declaration::Constructor {
                inductive,
                num_fields,
                ..
            }) => (*inductive, usize::from(*num_fields)),
            _ => return false,
        };
        let (num_params, eligible) = match self.env.get(inductive) {
            Some(Declaration::Inductive {
                num_params,
                num_indices,
                is_recursive,
                ctor_names,
                ..
            }) => (
                usize::from(*num_params),
                *num_indices == 0 && !*is_recursive && ctor_names.as_slice() == [*ctor_name],
            ),
            _ => return false,
        };
        if !eligible || args.len() != num_params + num_fields {
            return false;
        }

        let Ok(structure_type) = self.infer_core(structure, ctx) else {
            return false;
        };
        let Ok(constructor_type) = self.infer_core(constructor_app, ctx) else {
            return false;
        };
        if !self.def_eq_core(structure_type, constructor_type, ctx) {
            return false;
        }

        for (field_index, &field) in args.iter().skip(num_params).enumerate() {
            let Ok(field_index) = u32::try_from(field_index) else {
                return false;
            };
            let projection = self.proj(inductive, field_index, structure);
            if !self.def_eq_core(projection, field, ctx) {
                return false;
            }
        }
        true
    }

    /// Proof irrelevance (nanoda's `proof_irrel_eq`): if both `x` and `y` are
    /// proofs (their inferred type is a `Prop`, i.e. inhabits `Sort 0`), they
    /// are def-eq when their types are def-eq.
    ///
    /// This stays within the environment-free fragment: it needs only `infer`
    /// + WHNF of the type to `Sort 0`, both in scope.
    fn proof_irrel_eq(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        let Some(x_ty) = self.proof_type(x, ctx) else {
            return false;
        };
        let Some(y_ty) = self.proof_type(y, ctx) else {
            return false;
        };
        self.def_eq_core(x_ty, y_ty, ctx)
    }

    /// If `e` is a proof, return its type; otherwise `None`. `e` is a proof iff
    /// its type's type WHNFs to `Sort 0` (it inhabits a `Prop`). Inference
    /// failures (e.g. out-of-scope `Const`) yield `None` — proof irrelevance is
    /// then simply not applied, never an error.
    fn proof_type(&mut self, e: ExprId, ctx: &mut LocalContext) -> Option<ExprId> {
        let ty = self.infer_core(e, ctx).ok()?;
        let sort = self.infer_core(ty, ctx).ok()?;
        let sort = self.whnf_core(sort, ctx);
        match self.expr_node(sort) {
            ExprNode::Sort(level) => {
                let l = *level;
                if self.level_is_zero(l) {
                    Some(ty)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Definitional equality for the environment-free fragment.
    ///
    /// Entry point; allocates a fresh [`LocalContext`]. Use
    /// [`Kernel::def_eq_in`] to share an existing context (e.g. while already
    /// under binders).
    #[must_use]
    pub fn def_eq(&mut self, x: ExprId, y: ExprId) -> bool {
        let mut ctx = LocalContext::new();
        self.def_eq_core(x, y, &mut ctx)
    }

    /// Definitional equality in an existing local context.
    #[must_use]
    pub fn def_eq_in(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        self.def_eq_core(x, y, ctx)
    }

    /// The same-const short-circuit (nanoda's `try_eq_const_app`): when both
    /// sides apply the **same** `Regular` definition with **equal** hints, try
    /// to show equality by comparing the spine arguments and universe levels
    /// directly, *before* unfolding either side. Returns `Some(true)` on a
    /// match, `None` to fall through to unfolding.
    ///
    /// This only fires for `Regular`/`Regular` with identical hints (so that
    /// the cheap congruence is a sound shortcut for two copies of the same
    /// definition); `Theorem`/`Opaque` (`Opaque` hint) do not take this path.
    ///
    /// The argument list mirrors nanoda's `try_eq_const_app` (both heads, both
    /// names, and both hints), hence the lint allowance.
    #[allow(clippy::too_many_arguments)]
    fn try_eq_const_app(
        &mut self,
        x: ExprId,
        x_name: NameId,
        x_hint: ReducibilityHint,
        y: ExprId,
        y_name: NameId,
        y_hint: ReducibilityHint,
        ctx: &mut LocalContext,
    ) -> Option<bool> {
        if x_name != y_name {
            return None;
        }
        if !matches!(
            (x_hint, y_hint),
            (ReducibilityHint::Regular(_), ReducibilityHint::Regular(_))
        ) {
            return None;
        }
        if x_hint != y_hint {
            return None;
        }
        let (lf, largs) = self.unfold_apps(x);
        let (rf, rargs) = self.unfold_apps(y);
        let (ExprNode::Const(_, llevels), ExprNode::Const(_, rlevels)) =
            (self.expr_node(lf).clone(), self.expr_node(rf).clone())
        else {
            return None;
        };
        if largs.len() != rargs.len() || llevels.len() != rlevels.len() {
            return None;
        }
        let args_eq = largs
            .iter()
            .zip(rargs.iter())
            .all(|(&a, &b)| self.def_eq_core(a, b, ctx));
        if !args_eq {
            return None;
        }
        let levels_eq = llevels
            .iter()
            .zip(rlevels.iter())
            .all(|(&a, &b)| self.level_is_equiv(a, b));
        if levels_eq { Some(true) } else { None }
    }

    /// The lazy-delta loop (nanoda's `lazy_delta_step`): if either side has an
    /// unfoldable `Const` head, unfold the **higher-height** side to bring the
    /// two closer, short-circuiting via [`Kernel::try_eq_const_app`] when both
    /// apply the same definition. Returns `FoundEqResult(b)` when a cheap
    /// answer is reached, or `Exhausted(x, y)` (neither side unfoldable) to
    /// hand back to the structural checks.
    fn lazy_delta_step(
        &mut self,
        mut x: ExprId,
        mut y: ExprId,
        ctx: &mut LocalContext,
    ) -> DeltaResult {
        loop {
            if let Some(result) = self.def_eq_nat_offset(x, y, ctx) {
                return DeltaResult::FoundEqResult(result);
            }
            // Lean's `lazy_delta_reduction` (`type_checker.cpp:971-984`): after
            // offset equality and **before** the δ step, try the literal-`Nat`
            // acceleration on either side — but only when *neither* side
            // mentions a free variable. That guard is verbatim Lean's
            // `(!has_fvar(t_n) && !has_fvar(s_n))` at `:978`; Lean's `m_eager_reduce`
            // disjunct is an elaborator-only mode this kernel does not have.
            //
            // Without this site the rule would be unreachable from the route
            // that matters: `def_eq_core_uncached` normalises both sides with
            // `whnf_no_unfolding` (Lean's `whnf_core`, which carries no `Nat`
            // rule) and then comes straight here, so `Nat.add 2 3 =?= 5` would
            // grind through `Nat.add`'s recursive definition — exactly the
            // pathology ADR-0459 exists to remove.
            if !self.has_fvars(x) && !self.has_fvars(y) {
                if let Some(reduced) = self.reduce_nat_binop(x, ctx) {
                    return DeltaResult::FoundEqResult(self.def_eq_core(reduced, y, ctx));
                } else if let Some(reduced) = self.reduce_nat_binop(y, ctx) {
                    return DeltaResult::FoundEqResult(self.def_eq_core(x, reduced, ctx));
                }
            }
            let r1 = self.get_applied_def(x);
            let r2 = self.get_applied_def(y);
            match (r1, r2) {
                (None, None) => return DeltaResult::Exhausted(x, y),
                (Some(_), None) => x = self.delta(x, ctx),
                (None, Some(_)) => y = self.delta(y, ctx),
                (Some((_, l_hint)), Some((_, r_hint))) if l_hint.is_lt(r_hint) => {
                    y = self.delta(y, ctx);
                }
                (Some((_, l_hint)), Some((_, r_hint))) if r_hint.is_lt(l_hint) => {
                    x = self.delta(x, ctx);
                }
                (Some((x_name, l_hint)), Some((y_name, r_hint))) => {
                    if let Some(r) =
                        self.try_eq_const_app(x, x_name, l_hint, y, y_name, r_hint, ctx)
                    {
                        return DeltaResult::FoundEqResult(r);
                    }
                    x = self.delta(x, ctx);
                    y = self.delta(y, ctx);
                }
            }
            if let Some(quick) = self.def_eq_quick(x, y, ctx) {
                return DeltaResult::FoundEqResult(quick);
            }
        }
    }

    /// The lazy structural algorithm (nanoda's `def_eq`/`def_eq_core`): quick
    /// check, WHNF-without-δ both sides, quick check again, proof irrelevance,
    /// then the **lazy-delta step** (δ-unfolding with height-driven side
    /// choice), and finally the structural checks (`Const`, `FVar`, `App`
    /// spine, function eta, structure eta) on the delta-exhausted heads.
    fn def_eq_core(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        if let Some(quick) = self.def_eq_quick(x, y, ctx) {
            return quick;
        }
        if let Some(result) = ctx.def_eq_result(x, y) {
            return result;
        }
        let mark = ctx.unbound_probe_mark();
        let result = self.def_eq_core_uncached(x, y, ctx);
        ctx.remember_def_eq(x, y, result);
        ctx.taint_def_eq_if_unbound_probed(mark, x, y);
        result
    }

    fn def_eq_core_uncached(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        if let Some(quick) = self.def_eq_quick(x, y, ctx) {
            return quick;
        }

        // WHNF without δ — δ is handled lazily by `lazy_delta_step` below so
        // that we unfold only as far as needed (matching nanoda).
        let x_n = self.whnf_no_unfolding(x, ctx);
        let y_n = self.whnf_no_unfolding(y, ctx);

        if let Some(quick) = self.def_eq_quick(x_n, y_n, ctx) {
            return quick;
        }

        if self.proof_irrel_eq(x_n, y_n, ctx) {
            return true;
        }

        match self.lazy_delta_step(x_n, y_n, ctx) {
            DeltaResult::FoundEqResult(b) => b,
            DeltaResult::Exhausted(x_n, y_n) => {
                if self.def_eq_const(x_n, y_n) || self.def_eq_fvar(x_n, y_n) {
                    return true;
                }
                // Ordered as in Lean: `a.i =?= b.i` is tried as `a =?= b`
                // before the spine congruence below, which cannot see through a
                // stuck projection at all.
                if self.def_eq_proj(x_n, y_n, ctx) {
                    return true;
                }
                if self.def_eq_app(x_n, y_n, ctx) {
                    return true;
                }
                if self.try_eta_expansion(x_n, y_n, ctx) {
                    return true;
                }
                if self.try_eta_structure(x_n, y_n, ctx) {
                    return true;
                }
                // Lean's `is_def_eq_core` tries the String-literal expansion
                // here — after eta, on the delta-exhausted heads — and this
                // placement is deliberate rather than convenient: trying it
                // earlier would identify terms the pinned kernel leaves
                // distinct.
                if let Some(result) = self.try_string_lit_expansion(x_n, y_n, ctx) {
                    return result;
                }
                false
            }
        }
    }
}

/// The outcome of [`Kernel::lazy_delta_step`]: either a cheap equality verdict
/// (`FoundEqResult`) or the delta-exhausted head pair to hand to the structural
/// checks (`Exhausted`). Ported from nanoda's `DeltaResult`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeltaResult {
    FoundEqResult(bool),
    Exhausted(ExprId, ExprId),
}

/// Checked environment/type-spine facts needed to walk one projection's sole
/// constructor telescope. Kept private so callers cannot manufacture trusted
/// structure metadata outside the inductive admission gate.
struct ProjectionInferenceData {
    ctor_name: NameId,
    num_params: usize,
    levels: Vec<LevelId>,
    type_args: Vec<ExprId>,
}

/// Checked reserved declarations used by primitive Nat literal semantics.
#[derive(Debug, Clone, Copy)]
struct NatLiteralBootstrap {
    zero: NameId,
    succ: NameId,
    nat_type: ExprId,
}

/// One constructor layer of a compact Nat value.
enum NatOffset {
    Zero,
    Succ(ExprId),
}

/// Checked reserved declarations used by primitive `String` literal semantics
/// (ADR-0366).
///
/// Every handle here was *read out of the environment's own declared types*
/// rather than built locally, so validating the bootstrap interns nothing —
/// see [`Kernel::string_literal_bootstrap`] for why that matters.
#[derive(Debug, Clone, Copy)]
pub(crate) struct StringLiteralBootstrap {
    /// `String`, as the already-interned `Const String []` a literal infers to.
    string_type: ExprId,
    /// `Char`, as the already-interned `Const Char []` that instantiates `List`.
    char_type: ExprId,
    /// The universe argument `List` is applied at in `List Char` (Lean's `0`).
    list_level: LevelId,
    /// `String.ofList : List Char → String`.
    of_list: NameId,
    /// `Char.ofNat : Nat → Char`.
    char_of_nat: NameId,
    /// `List.nil`.
    list_nil: NameId,
    /// `List.cons`.
    list_cons: NameId,
}

/// `None` when the environment carries no validated `String` bootstrap, in which
/// case no string literal types and no expansion fires.
pub(crate) type StringLiteralTable = Option<StringLiteralBootstrap>;

/// Lean's `ReducePowMaxExp` (`kernel/type_checker.cpp`): the exponent above
/// which `Nat.pow` is left stuck rather than evaluated. Reused as the shift
/// bound, which Lean does not bound but which is the same memory bomb; a bound
/// only ever refuses a reduction, so it is fail-closed relative to Lean.
const REDUCE_POW_MAX_EXPONENT: u32 = 1 << 24;

/// A binary `Nat` operation the kernel evaluates directly on literal arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NatBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Gcd,
    Pow,
    Land,
    Lor,
    Xor,
    ShiftLeft,
    ShiftRight,
    Beq,
    Ble,
}

/// The checked declarations behind literal `Nat` arithmetic.
#[derive(Debug, Clone)]
pub(crate) struct NatBinOpEntries {
    /// Environment declarations accepted as each operation, by name.
    ops: HashMap<NameId, NatBinOp>,
    /// `Nat.zero`, which reduction accepts in place of the literal `0`.
    zero: NameId,
    /// `Bool.true` / `Bool.false`, the results of the two predicates.
    bool_true: NameId,
    bool_false: NameId,
}

/// `None` when the environment carries no validated `Nat`/`Bool` bootstrap, in
/// which case no literal arithmetic fires.
pub(crate) type NatBinOpTable = Option<NatBinOpEntries>;

impl Kernel {
    /// Validate the reserved declarations on which primitive Nat literals
    /// depend. Official Lean inherits these from its bootstrap; Axeyum imports
    /// into a fresh environment and therefore checks the shape explicitly.
    fn nat_literal_bootstrap(&mut self) -> Result<NatLiteralBootstrap, KernelError> {
        let anon = self.anon();
        let nat = self.name_str(anon, "Nat");
        let zero = self.name_str(nat, "zero");
        let succ = self.name_str(nat, "succ");
        let level_zero = self.level_zero();
        let level_one = self.level_succ(level_zero);
        let expected_inductive_type = self.sort(level_one);
        let nat_type = self.const_(nat, vec![]);

        let inductive_ok = matches!(
            self.env.get(nat),
            Some(Declaration::Inductive {
                uparams,
                ty,
                num_params: 0,
                num_indices: 0,
                is_recursive: true,
                ctor_names,
                ..
            }) if uparams.is_empty()
                && *ty == expected_inductive_type
                && ctor_names.as_slice() == [zero, succ]
        );
        let zero_ok = matches!(
            self.env.get(zero),
            Some(Declaration::Constructor {
                uparams,
                ty,
                inductive,
                idx: 0,
                num_fields: 0,
                ..
            }) if uparams.is_empty() && *ty == nat_type && *inductive == nat
        );
        let succ_type = match self.env.get(succ) {
            Some(Declaration::Constructor {
                uparams,
                ty,
                inductive,
                idx: 1,
                num_fields: 1,
                ..
            }) if uparams.is_empty() && *inductive == nat => Some(*ty),
            _ => None,
        };
        let succ_ok = succ_type.is_some_and(|ty| {
            matches!(
                self.expr_node(ty),
                ExprNode::Pi(_, domain, body, BinderInfo::Default)
                    if *domain == nat_type && *body == nat_type
            )
        });

        if !(inductive_ok && zero_ok && succ_ok) {
            return Err(KernelError::NatLiteralBootstrapMismatch { nat });
        }
        Ok(NatLiteralBootstrap {
            zero,
            succ,
            nat_type,
        })
    }

    fn infer_nat_literal(&mut self) -> Result<ExprId, KernelError> {
        Ok(self.nat_literal_bootstrap()?.nat_type)
    }

    fn nat_offset(
        &mut self,
        expression: ExprId,
        bootstrap: NatLiteralBootstrap,
    ) -> Option<NatOffset> {
        if let ExprNode::Lit(Lit::Nat(value)) = self.expr_node(expression).clone() {
            return match value.predecessor() {
                Some(predecessor) => Some(NatOffset::Succ(self.lit(Lit::Nat(predecessor)))),
                None => Some(NatOffset::Zero),
            };
        }

        let (head, arguments) = self.unfold_apps(expression);
        let ExprNode::Const(name, levels) = self.expr_node(head) else {
            return None;
        };
        if !levels.is_empty() {
            return None;
        }
        if *name == bootstrap.zero && arguments.is_empty() {
            Some(NatOffset::Zero)
        } else if *name == bootstrap.succ && arguments.len() == 1 {
            Some(NatOffset::Succ(arguments[0]))
        } else {
            None
        }
    }

    /// Lean's offset equality: compact literals and unary constructors expose
    /// one zero/successor layer, then ordinary definitional equality compares
    /// the predecessors.
    fn def_eq_nat_offset(
        &mut self,
        left: ExprId,
        right: ExprId,
        ctx: &mut LocalContext,
    ) -> Option<bool> {
        let bootstrap = self.nat_literal_bootstrap().ok()?;
        match (
            self.nat_offset(left, bootstrap)?,
            self.nat_offset(right, bootstrap)?,
        ) {
            (NatOffset::Zero, NatOffset::Zero) => Some(true),
            (NatOffset::Succ(left), NatOffset::Succ(right)) => {
                Some(self.def_eq_core(left, right, ctx))
            }
            _ => None,
        }
    }

    /// The TL2.7 constructor conversion subset of Lean's Nat reducer.
    /// General arithmetic operations remain TL2.8.
    fn reduce_nat_succ(&mut self, expression: ExprId, ctx: &mut LocalContext) -> Option<ExprId> {
        let bootstrap = self.nat_literal_bootstrap().ok()?;
        let (head, arguments) = self.unfold_apps(expression);
        let ExprNode::Const(name, levels) = self.expr_node(head) else {
            return None;
        };
        if *name != bootstrap.succ || !levels.is_empty() || arguments.len() != 1 {
            return None;
        }
        let argument = self.whnf_core(arguments[0], ctx);
        let ExprNode::Lit(Lit::Nat(value)) = self.expr_node(argument).clone() else {
            return None;
        };
        Some(self.lit(Lit::Nat(value.successor())))
    }

    /// Expose one constructor layer for Nat recursor reduction, matching
    /// Lean's `nat_lit_to_constructor` helper.
    pub(crate) fn nat_literal_to_constructor(&mut self, expression: ExprId) -> Option<ExprId> {
        let bootstrap = self.nat_literal_bootstrap().ok()?;
        let ExprNode::Lit(Lit::Nat(value)) = self.expr_node(expression).clone() else {
            return None;
        };
        match value.predecessor() {
            None => Some(self.const_(bootstrap.zero, vec![])),
            Some(predecessor) => {
                let succ = self.const_(bootstrap.succ, vec![]);
                let predecessor = self.lit(Lit::Nat(predecessor));
                Some(self.app(succ, predecessor))
            }
        }
    }

    /// Lean's `is_nat_lit_ext`: a `Nat` literal, or the constant `Nat.zero`,
    /// which is the same value written the other way.
    fn nat_literal_ext(&mut self, expression: ExprId, zero: NameId) -> Option<NatLit> {
        match self.expr_node(expression) {
            ExprNode::Lit(Lit::Nat(value)) => Some(value.clone()),
            ExprNode::Const(name, levels) if *name == zero && levels.is_empty() => {
                Some(NatLit::from(0_u8))
            }
            _ => None,
        }
    }

    /// The binary `Nat` operations this kernel evaluates directly on literals,
    /// keyed by the environment's own declarations.
    ///
    /// Rebuilt when the environment revision moves, which is cheap: it is
    /// sixteen name lookups and sixteen shape checks. Absent (`None`) means the
    /// environment does not (yet) carry a validated `Nat`/`Bool` bootstrap, in
    /// which case no arithmetic fires at all.
    fn nat_binop_table(&mut self) -> Option<&NatBinOpEntries> {
        let revision = self.env.revision();
        if self.nat_binop_cache.as_ref().map(|(rev, _)| *rev) != Some(revision) {
            let table = self.build_nat_binop_table();
            self.nat_binop_cache = Some((revision, table));
        }
        self.nat_binop_cache.as_ref().and_then(|(_, t)| t.as_ref())
    }

    /// Check the shapes the literal arithmetic rules stand on.
    ///
    /// Every entry is admitted only if the environment declares it as a
    /// `Definition` (never an axiom or an opaque), with **no universe
    /// parameters** and with exactly Lean's type — `Nat → Nat → Nat` for the
    /// arithmetic and bitwise operations, `Nat → Nat → Bool` for the two
    /// predicates. `Bool` itself is checked the way `nat_literal_bootstrap`
    /// checks `Nat`: a parameter-free, index-free, non-recursive inductive in
    /// `Type` whose constructors are exactly `[Bool.false, Bool.true]` in that
    /// order, both nullary. A missing or differently-shaped declaration simply
    /// leaves that operation unaccelerated; nothing is assumed into existence.
    fn build_nat_binop_table(&mut self) -> NatBinOpTable {
        let literal = self.nat_literal_bootstrap().ok()?;
        let anon = self.anon();
        // Lookups, never interning: see `Kernel::lookup_name_str`. A name this
        // environment has never heard of cannot be the operation we are looking
        // for, so absence is simply "no rule".
        let nat = self.lookup_name_str(anon, "Nat")?;
        let bool_name = self.lookup_name_str(anon, "Bool")?;
        let bool_false = self.lookup_name_str(bool_name, "false")?;
        let bool_true = self.lookup_name_str(bool_name, "true")?;

        // Shape first, interning second. `sort`/`const_` mint an expression when
        // one does not already exist, which renumbers an export just as name
        // interning does; both ids below are provably already present *given*
        // that this really is Lean's `Bool` (its declared type IS `Sort 1` and
        // its constructors' types ARE `Bool`), so the checks are ordered to
        // establish that before either is built.
        let declared_bool = matches!(
            self.env.get(bool_name),
            Some(Declaration::Inductive {
                uparams,
                num_params: 0,
                num_indices: 0,
                is_recursive: false,
                ctor_names,
                ..
            }) if uparams.is_empty() && ctor_names.as_slice() == [bool_false, bool_true]
        );
        if !declared_bool {
            return None;
        }
        let level_zero = self.level_zero();
        let level_one = self.level_succ(level_zero);
        let type0 = self.sort(level_one);
        let bool_type = self.const_(bool_name, vec![]);
        let bool_ok = matches!(
            self.env.get(bool_name),
            Some(Declaration::Inductive { ty, .. }) if *ty == type0
        ) && [bool_false, bool_true]
            .iter()
            .enumerate()
            .all(|(idx, ctor)| {
                matches!(
                    self.env.get(*ctor),
                    Some(Declaration::Constructor {
                        uparams,
                        ty,
                        inductive,
                        num_fields: 0,
                        idx: got,
                        ..
                    }) if uparams.is_empty()
                        && *ty == bool_type
                        && *inductive == bool_name
                        && usize::from(*got) == idx
                )
            });
        if !bool_ok {
            return None;
        }

        // `Nat → Nat → Nat` and `Nat → Nat → Bool`. Checked by walking the two
        // Pi layers rather than by comparing interned ids: binder *names* are
        // part of an interned `Pi` node, and the official export spells
        // `Nat.add`'s type with named binders, so an id comparison against a
        // locally built arrow would silently never match. Binder annotations are
        // likewise ignored — they do not affect definitional equality.
        let nat_type = literal.nat_type;

        let mut ops = HashMap::new();
        for (segment, op, result) in [
            ("add", NatBinOp::Add, nat_type),
            ("sub", NatBinOp::Sub, nat_type),
            ("mul", NatBinOp::Mul, nat_type),
            ("div", NatBinOp::Div, nat_type),
            ("mod", NatBinOp::Mod, nat_type),
            ("gcd", NatBinOp::Gcd, nat_type),
            ("pow", NatBinOp::Pow, nat_type),
            ("land", NatBinOp::Land, nat_type),
            ("lor", NatBinOp::Lor, nat_type),
            ("xor", NatBinOp::Xor, nat_type),
            ("shiftLeft", NatBinOp::ShiftLeft, nat_type),
            ("shiftRight", NatBinOp::ShiftRight, nat_type),
            ("beq", NatBinOp::Beq, bool_type),
            ("ble", NatBinOp::Ble, bool_type),
        ] {
            let Some(name) = self.lookup_name_str(nat, segment) else {
                continue;
            };
            let declared = match self.env.get(name) {
                Some(Declaration::Definition { uparams, ty, .. }) if uparams.is_empty() => *ty,
                _ => continue,
            };
            if self.is_binary_nat_operation(declared, nat_type, result) {
                ops.insert(name, op);
            }
        }

        Some(NatBinOpEntries {
            ops,
            zero: literal.zero,
            bool_true,
            bool_false,
        })
    }

    /// Whether `ty` is exactly `nat → nat → result`, ignoring binder names and
    /// annotations (neither affects definitional equality) but requiring the
    /// codomain to be non-dependent — a `Pi` whose body mentions its binder is
    /// not this shape and gets no reduction rule.
    fn is_binary_nat_operation(&self, ty: ExprId, nat: ExprId, result: ExprId) -> bool {
        let ExprNode::Pi(_, first_domain, first_body, _) = self.expr_node(ty) else {
            return false;
        };
        let (first_domain, first_body) = (*first_domain, *first_body);
        if first_domain != nat {
            return false;
        }
        let ExprNode::Pi(_, second_domain, second_body, _) = self.expr_node(first_body) else {
            return false;
        };
        *second_domain == nat && *second_body == result
    }

    /// Lean's `type_checker::reduce_nat` for the two-argument cases: a fully
    /// applied `Nat` operation whose arguments both normalize to literals is
    /// evaluated directly instead of unfolding its recursive definition.
    ///
    /// **This is what makes real Lean exports checkable at all.** `Char`,
    /// `UInt8/16/32/64`, `USize` and `Fin` are `Nat` under bounds like `2^32`
    /// and `1114112`, and reaching those by `Nat.succ` steps is not slow but
    /// unbounded: measured 2026-08-15, `Option.repr` and
    /// `Lean.Parser.Attr.extIff` each exhausted an 8 GB address space in under
    /// two minutes without this rule and import in under a second with it.
    ///
    /// The trust this adds is exactly Lean's, and it is worth naming: the rule
    /// is keyed on the *name* `Nat.add`, so an environment that declared some
    /// other function under that name (with the right type) would be evaluated
    /// as addition. `build_nat_binop_table` narrows that to a definition of the
    /// exact expected type, and `nat_binop_agrees_with_unaccelerated_reduction`
    /// pins the semantics against the imported `Init` definitions themselves.
    fn reduce_nat_binop(&mut self, expression: ExprId, ctx: &mut LocalContext) -> Option<ExprId> {
        let (head, arguments) = self.unfold_apps(expression);
        if arguments.len() != 2 {
            return None;
        }
        let ExprNode::Const(name, levels) = self.expr_node(head) else {
            return None;
        };
        if !levels.is_empty() {
            return None;
        }
        let name = *name;
        let table = self.nat_binop_table()?;
        let op = table.ops.get(&name).copied()?;
        let zero = table.zero;
        let bool_true = table.bool_true;
        let bool_false = table.bool_false;

        let left = self.whnf_core(arguments[0], ctx);
        let left = self.nat_literal_ext(left, zero)?;
        let right = self.whnf_core(arguments[1], ctx);
        let right = self.nat_literal_ext(right, zero)?;

        let value = match op {
            NatBinOp::Add => left.checked_add(&right),
            NatBinOp::Sub => left.truncated_sub(&right),
            NatBinOp::Mul => left.checked_mul(&right),
            NatBinOp::Div => left.lean_div(&right),
            NatBinOp::Mod => left.lean_mod(&right),
            NatBinOp::Gcd => left.gcd(&right),
            NatBinOp::Pow => left.bounded_pow(&right, REDUCE_POW_MAX_EXPONENT)?,
            NatBinOp::Land => left.bitand(&right),
            NatBinOp::Lor => left.bitor(&right),
            NatBinOp::Xor => left.bitxor(&right),
            NatBinOp::ShiftLeft => left.bounded_shl(&right, REDUCE_POW_MAX_EXPONENT)?,
            NatBinOp::ShiftRight => left.shr(&right),
            NatBinOp::Beq => {
                let ctor = if left == right { bool_true } else { bool_false };
                return Some(self.const_(ctor, vec![]));
            }
            NatBinOp::Ble => {
                let ctor = if left <= right { bool_true } else { bool_false };
                return Some(self.const_(ctor, vec![]));
            }
        };
        Some(self.lit(Lit::Nat(value)))
    }
}

// ---------------------------------------------------------------------------
// Primitive String literal semantics (ADR-0366)
// ---------------------------------------------------------------------------

impl Kernel {
    /// The checked `String` bootstrap for this environment revision, or `None`
    /// when the environment does not carry one.
    pub(crate) fn string_literal_bootstrap(&mut self) -> Option<StringLiteralBootstrap> {
        let revision = self.env.revision();
        if self.string_literal_cache.as_ref().map(|(rev, _)| *rev) != Some(revision) {
            let table = self.build_string_literal_bootstrap();
            self.string_literal_cache = Some((revision, table));
        }
        self.string_literal_cache.as_ref().and_then(|(_, t)| *t)
    }

    /// Validate every reserved declaration the primitive `String` rules stand
    /// on, and return the handles they need.
    ///
    /// Official Lean starts with these installed and its kernel simply trusts
    /// the names. Axeyum imports into a fresh environment, so spelling alone
    /// would let a declaration chosen by the *stream* decide what a literal
    /// means. The gate therefore requires, with no partial state stored:
    ///
    /// - the already-checked canonical `Nat` bootstrap (`Char.ofNat`'s domain);
    /// - `String.ofList` to be a `Definition` with **no** universe parameters
    ///   and exactly the type `List Char → String`;
    /// - `Char.ofNat` to be a `Definition` with no universe parameters and
    ///   exactly the type `Nat → Char`, for the *same* `Char`;
    /// - `List` to be the one-parameter, index-free, recursive inductive at one
    ///   universe parameter whose constructors are `[List.nil, List.cons]` with
    ///   field counts 0 and 2 at indices 0 and 1;
    /// - `Char` to be a parameter-free, index-free, non-recursive inductive with
    ///   the single constructor `Char.mk`; and
    /// - `String` likewise, with the single constructor `String.ofByteArray`
    ///   (Lean 4.30's representation: `String` is a *structure over `ByteArray`*,
    ///   and `String.ofList` is a **definition**, not its constructor).
    ///
    /// **Nothing here is interned.** Names are looked up
    /// ([`Kernel::lookup_name_str`]), and every expression handle returned is
    /// read back out of a declared type rather than built — `Const String []`
    /// is the codomain of `String.ofList`'s own declared type, `Const Char []`
    /// its domain's argument. Minting a name renumbers a subsequent export (the
    /// `Nat` acceleration lane shipped exactly that bug and the round-trip gate
    /// caught it), and this runs on every literal that reaches inference.
    ///
    /// The inherited `Nat` gate does intern its three canonical names, so it is
    /// consulted **after** the string-specific lookups have established that
    /// this environment could plausibly be Lean's: an environment that has never
    /// heard of `String.ofList` leaves this function having interned nothing.
    fn build_string_literal_bootstrap(&mut self) -> StringLiteralTable {
        let anon = self.anon();
        let string_name = self.lookup_name_str(anon, "String")?;
        let char_name = self.lookup_name_str(anon, "Char")?;
        let list_name = self.lookup_name_str(anon, "List")?;
        let of_list = self.lookup_name_str(string_name, "ofList")?;
        let of_byte_array = self.lookup_name_str(string_name, "ofByteArray")?;
        let char_mk = self.lookup_name_str(char_name, "mk")?;
        let char_of_nat = self.lookup_name_str(char_name, "ofNat")?;
        let list_nil = self.lookup_name_str(list_name, "nil")?;
        let list_cons = self.lookup_name_str(list_name, "cons")?;
        let nat = self.nat_literal_bootstrap().ok()?;

        // `Char.ofNat : Nat → Char`, which is where `Char` comes from.
        let char_of_nat_ty = match self.env.get(char_of_nat) {
            Some(Declaration::Definition { uparams, ty, .. }) if uparams.is_empty() => *ty,
            _ => return None,
        };
        let ExprNode::Pi(_, domain, char_type, _) = self.expr_node(char_of_nat_ty) else {
            return None;
        };
        let (domain, char_type) = (*domain, *char_type);
        if domain != nat.nat_type || !self.is_bare_const(char_type, char_name) {
            return None;
        }

        // `String.ofList : List Char → String`, which is where `String`, the
        // `List` universe argument, and the second reading of `Char` come from.
        let of_list_ty = match self.env.get(of_list) {
            Some(Declaration::Definition { uparams, ty, .. }) if uparams.is_empty() => *ty,
            _ => return None,
        };
        let ExprNode::Pi(_, list_char, string_type, _) = self.expr_node(of_list_ty) else {
            return None;
        };
        let (list_char, string_type) = (*list_char, *string_type);
        if !self.is_bare_const(string_type, string_name) {
            return None;
        }
        let ExprNode::App(list_head, list_arg) = self.expr_node(list_char) else {
            return None;
        };
        let (list_head, list_arg) = (*list_head, *list_arg);
        if list_arg != char_type {
            return None;
        }
        let ExprNode::Const(head_name, head_levels) = self.expr_node(list_head) else {
            return None;
        };
        if *head_name != list_name || head_levels.len() != 1 {
            return None;
        }
        let list_level = head_levels[0];
        if !matches!(self.level_node(list_level), LevelNode::Zero) {
            return None;
        }

        // `List`: one universe parameter, one parameter, no indices, recursive,
        // constructors `[nil, cons]` with 0 and 2 fields at indices 0 and 1.
        let list_ok = matches!(
            self.env.get(list_name),
            Some(Declaration::Inductive {
                uparams,
                num_params: 1,
                num_indices: 0,
                is_recursive: true,
                ctor_names,
                ..
            }) if uparams.len() == 1 && ctor_names.as_slice() == [list_nil, list_cons]
        ) && self.is_constructor_of(list_nil, list_name, 0, 0)
            && self.is_constructor_of(list_cons, list_name, 1, 2);
        if !list_ok {
            return None;
        }

        // `Char` and `String`: parameter-free, index-free, non-recursive
        // one-constructor structures with Lean 4.30's constructor names.
        if !(self.is_structure_with_sole_constructor(char_name, char_mk)
            && self.is_structure_with_sole_constructor(string_name, of_byte_array))
        {
            return None;
        }

        Some(StringLiteralBootstrap {
            string_type,
            char_type,
            list_level,
            of_list,
            char_of_nat,
            list_nil,
            list_cons,
        })
    }

    /// Whether `expression` is exactly `Const(name, [])`.
    fn is_bare_const(&self, expression: ExprId, name: NameId) -> bool {
        matches!(
            self.expr_node(expression),
            ExprNode::Const(got, levels) if *got == name && levels.is_empty()
        )
    }

    /// Whether `ctor` is the checked constructor of `inductive` at `idx` with
    /// exactly `num_fields` fields (universe parameters are shared with the
    /// parent and are checked there).
    fn is_constructor_of(
        &self,
        ctor: NameId,
        inductive: NameId,
        idx: u16,
        num_fields: u16,
    ) -> bool {
        matches!(
            self.env.get(ctor),
            Some(Declaration::Constructor {
                inductive: parent,
                idx: got_idx,
                num_fields: got_fields,
                ..
            }) if *parent == inductive && *got_idx == idx && *got_fields == num_fields
        )
    }

    /// Whether `name` is a parameter-free, index-free, non-recursive inductive
    /// whose sole constructor is `ctor` — Lean's `structure`, with the exact
    /// constructor name pinned.
    fn is_structure_with_sole_constructor(&self, name: NameId, ctor: NameId) -> bool {
        matches!(
            self.env.get(name),
            Some(Declaration::Inductive {
                uparams,
                num_params: 0,
                num_indices: 0,
                is_recursive: false,
                ctor_names,
                ..
            }) if uparams.is_empty() && ctor_names.as_slice() == [ctor]
        )
    }

    /// Lean's `Literal.type` for `.strVal`, gated on the checked bootstrap.
    fn infer_string_literal(&mut self) -> Result<ExprId, KernelError> {
        if let Some(bootstrap) = self.string_literal_bootstrap() {
            return Ok(bootstrap.string_type);
        }
        let anon = self.anon();
        Err(KernelError::StringLiteralBootstrapMismatch {
            string: self.lookup_name_str(anon, "String"),
        })
    }

    /// Lean's `string_lit_to_constructor` (`kernel/inductive.cpp`): a literal
    /// becomes `String.ofList` applied to the `List Char` of its **Unicode
    /// scalar values**, in order, each wrapped by `Char.ofNat` around a `Nat`
    /// literal.
    ///
    /// Scalars, never bytes: `"é"` is one character `0xE9`, `"🙂"` is one
    /// character `0x1F642`, and `"e\u{301}"` stays two. Rust's `chars()` is
    /// exactly Lean's `utf8_decode` on a valid UTF-8 payload, and a Rust
    /// `String` cannot hold a lone surrogate.
    ///
    /// The result is **not** a constructor application. In Lean 4.30 `String` is
    /// a structure over `ByteArray` and `String.ofList` is an ordinary
    /// definition, so this term is δ-reducible rather than already in whnf —
    /// which is why every caller normalizes it before looking for a
    /// constructor, exactly as Lean's `whnf(string_lit_to_constructor(...))`
    /// does.
    pub(crate) fn string_literal_to_constructor(&mut self, expression: ExprId) -> Option<ExprId> {
        let ExprNode::Lit(Lit::Str(value)) = self.expr_node(expression).clone() else {
            return None;
        };
        let bootstrap = self.string_literal_bootstrap()?;
        let nil = self.const_(bootstrap.list_nil, vec![bootstrap.list_level]);
        let mut list = self.app(nil, bootstrap.char_type);
        let cons = self.const_(bootstrap.list_cons, vec![bootstrap.list_level]);
        let cons = self.app(cons, bootstrap.char_type);
        let of_nat = self.const_(bootstrap.char_of_nat, vec![]);
        for scalar in value.chars().rev() {
            let code = self.lit(Lit::Nat(NatLit::from(u32::from(scalar))));
            let character = self.app(of_nat, code);
            let step = self.app(cons, character);
            list = self.app(step, list);
        }
        let of_list = self.const_(bootstrap.of_list, vec![]);
        Some(self.app(of_list, list))
    }

    /// Normalize a string literal one constructor layer, for the reduction rules
    /// whose major/projected value may be a literal. Returns the input unchanged
    /// when it is not a literal or the environment carries no bootstrap.
    pub(crate) fn expand_string_literal_major(
        &mut self,
        expression: ExprId,
        ctx: &mut LocalContext,
    ) -> ExprId {
        match self.string_literal_to_constructor(expression) {
            Some(expanded) => self.whnf_core(expanded, ctx),
            None => expression,
        }
    }

    /// Lean's `try_string_lit_expansion`: a literal on one side and an
    /// **immediate** `String.ofList` application on the other are compared by
    /// expanding the literal. Symmetric in the two argument orders, and `None`
    /// when the shape does not apply so the caller falls through unchanged.
    ///
    /// **This rule is carried and unexercised, and that is a fact about Lean
    /// 4.30 rather than about this port** (ADR-0461). `is_def_eq_core` runs
    /// lazy delta first, and `String.ofList` is a *definition*, so a literal on
    /// one side forces the other to unfold to `String.ofByteArray` before the
    /// hook ever looks at it — the rule dates from when the constant it keys on
    /// was a constructor. What identifies a literal with a constructor
    /// application today is structure eta calling
    /// [`Kernel::expand_string_literal_major`] through the projection rule.
    /// Removing this function fails no test; it stays because the pinned source
    /// has it and its only possible effect is to accept *more*.
    fn try_string_lit_expansion(
        &mut self,
        x: ExprId,
        y: ExprId,
        ctx: &mut LocalContext,
    ) -> Option<bool> {
        if let Some(result) = self.try_string_lit_expansion_core(x, y, ctx) {
            return Some(result);
        }
        self.try_string_lit_expansion_core(y, x, ctx)
    }

    fn try_string_lit_expansion_core(
        &mut self,
        literal: ExprId,
        other: ExprId,
        ctx: &mut LocalContext,
    ) -> Option<bool> {
        if !matches!(self.expr_node(literal), ExprNode::Lit(Lit::Str(_))) {
            return None;
        }
        let bootstrap = self.string_literal_bootstrap()?;
        // Lean compares `app_fn(s)` against the bare constant `String.ofList`,
        // so this fires only on a one-argument application of it — never on a
        // partial application, an over-applied spine, or an alias.
        let ExprNode::App(head, _) = self.expr_node(other) else {
            return None;
        };
        if !self.is_bare_const(*head, bootstrap.of_list) {
            return None;
        }
        let expanded = self.string_literal_to_constructor(literal)?;
        let expanded = self.whnf_core(expanded, ctx);
        Some(self.def_eq_core(expanded, other, ctx))
    }
}

// ---------------------------------------------------------------------------
// Type inference
// ---------------------------------------------------------------------------

impl Kernel {
    /// Infer the type of `e` in a checking mode that validates as it goes.
    ///
    /// Allocates a fresh [`LocalContext`]; use [`Kernel::infer_in`] to share an
    /// existing one.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError`] for ill-typed or out-of-scope input: a non-`Pi`
    /// applied as a function ([`KernelError::NotAPi`]), a binder domain that is
    /// not a type ([`KernelError::NotASort`]), an argument or `let`-value type
    /// mismatch ([`KernelError::TypeMismatch`]), an invalid projection, a loose `BVar`
    /// ([`KernelError::LooseBVar`]), an unbound `FVar`
    /// ([`KernelError::UnboundFVar`]), an unknown `Const`
    /// ([`KernelError::UnknownConst`]), or a `Lit`
    /// whose reserved bootstrap is absent or malformed
    /// ([`KernelError::NatLiteralBootstrapMismatch`],
    /// [`KernelError::StringLiteralBootstrapMismatch`]).
    pub fn infer(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        let mut ctx = LocalContext::new();
        self.infer_core(e, &mut ctx)
    }

    /// Infer a proof skeleton whose selected lambda bodies already use their
    /// binders as free variables, then close those binders in one shared-DAG
    /// traversal.
    ///
    /// Each `(lambda, fvar)` marker gives `fvar` scope only inside that lambda's
    /// body. An occurrence outside its marked scope remains unbound and is
    /// rejected. The returned expression is produced by
    /// [`Kernel::close_scoped_fvars`], making this the bounded-memory equivalent
    /// of closing every lambda separately and then calling [`Kernel::infer`].
    ///
    /// # Errors
    ///
    /// Returns the ordinary [`KernelError`] when the scoped skeleton is
    /// ill-typed or a marked free variable escapes its owning lambda.
    ///
    /// # Panics
    ///
    /// Panics under the marker-contract violations documented by
    /// [`Kernel::close_scoped_fvars`], or when the same free variable is assigned
    /// to more than one lambda.
    pub fn infer_and_close_scoped_fvars(
        &mut self,
        expression: ExprId,
        binders: &[(ExprId, u64)],
    ) -> Result<(ExprId, ExprId), KernelError> {
        let mut ctx = LocalContext::new();
        for &(lambda, fvar) in binders {
            assert!(
                !ctx.scoped_fvars
                    .values()
                    .any(|&registered| registered == fvar),
                "a scoped free variable cannot belong to two lambdas"
            );
            assert!(
                ctx.scoped_fvars.insert(lambda, fvar).is_none(),
                "a lambda cannot bind two scoped free variables"
            );
        }
        let inferred = self.infer_core(expression, &mut ctx)?;
        let closed = self.close_scoped_fvars(expression, binders);
        Ok((closed, inferred))
    }

    /// Infer the type of `e` in an existing local context.
    ///
    /// # Errors
    ///
    /// As [`Kernel::infer`].
    pub fn infer_in(&mut self, e: ExprId, ctx: &mut LocalContext) -> Result<ExprId, KernelError> {
        self.infer_core(e, ctx)
    }

    /// Infer `e`, WHNF the result, and require it to be a `Sort`; return its
    /// level. (nanoda's `infer_sort_of` / `ensure_sort`.)
    fn infer_sort_of(&mut self, e: ExprId, ctx: &mut LocalContext) -> Result<LevelId, KernelError> {
        let ty = self.infer_core(e, ctx)?;
        let ty = self.whnf_core(ty, ctx);
        match self.expr_node(ty) {
            ExprNode::Sort(level) => Ok(*level),
            _ => Err(KernelError::NotASort { got: ty }),
        }
    }

    /// Check `expression` against an already known expected type.
    ///
    /// Lambda checking is bidirectional: compare its annotation with the
    /// expected `Pi`, open both bodies with one local, and check recursively.
    /// The fallback is the ordinary infer-then-definitional-equality rule. This
    /// is extensionally the same judgment, but it avoids constructing a second
    /// copy of a large dependent lambda telescope solely to compare it.
    pub(crate) fn check_core(
        &mut self,
        expression: ExprId,
        expected: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<(), KernelError> {
        let expected = self.whnf_core(expected, ctx);
        if let ExprNode::Lam(name, domain, body, info) = self.expr_node(expression).clone()
            && let ExprNode::Pi(_, expected_domain, expected_body, _) =
                self.expr_node(expected).clone()
        {
            // The binder domain must be a TYPE, not merely def-eq to the
            // expected one. Omitting this was a real divergence from the real
            // Lean kernel, found by
            // `axeyum-lean-import/tests/real_lean_wire_differential.rs`: an
            // ill-typed domain that BETA-REDUCES to the expected domain is
            // erased by `def_eq_core`'s whnf and was never checked at all.
            // Minimal case, accepted here and rejected by Lean 4.30.0's
            // `addDeclCore`:
            //
            //     h : (True -> True) -> True
            //     theorem t : True := h (fun (_ : (fun (x : Sort 1) => True) trivial) => trivial)
            //
            // `(fun (x : Sort 1) => True) trivial` is ill typed (`trivial :
            // True`, the binder wants `Sort 1`) and reduces to `True`.
            // `infer_lambda` has always checked this; this fast path bypassed
            // `infer_lambda` entirely, so the check has to be repeated here.
            // Lean's kernel has no such path: it infers and then `isDefEq`s,
            // and `inferLambda` calls `ensureSortCore` on the domain.
            self.infer_sort_of(domain, ctx)?;
            if !self.def_eq_core(domain, expected_domain, ctx) {
                return Err(KernelError::TypeMismatch {
                    expected: expected_domain,
                    got: domain,
                });
            }
            let scoped = ctx.scoped_fvar(expression);
            let fvar = scoped.unwrap_or_else(|| ctx.fresh_fvar());
            ctx.bump_fresh_above(fvar);
            let local = self.fvar(fvar);
            ctx.push(LocalDecl {
                fvar,
                name,
                ty: expected_domain,
                info,
            });
            let body = if scoped.is_some() {
                body
            } else {
                self.instantiate(body, &[local])
            };
            let expected_body = self.instantiate(expected_body, &[local]);
            let result = self.check_core(body, expected_body, ctx);
            ctx.pop();
            return result;
        }

        let inferred = self.infer_core(expression, ctx)?;
        if self.def_eq_core(inferred, expected, ctx) {
            Ok(())
        } else {
            Err(KernelError::TypeMismatch {
                expected,
                got: inferred,
            })
        }
    }

    pub(crate) fn infer_core(
        &mut self,
        e: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<ExprId, KernelError> {
        let closed = self.num_loose_bvars(e) == 0 && !self.has_fvars(e);
        if closed && let Some(&ty) = self.infer_closed_cache.get(&e) {
            return Ok(ty);
        }
        if !closed && let Some(ty) = ctx.inferred(e) {
            return Ok(ty);
        }
        let mark = ctx.unbound_probe_mark();
        let inferred = match self.expr_node(e).clone() {
            ExprNode::BVar(index) => Err(KernelError::LooseBVar { index }),
            ExprNode::FVar(id) => ctx.type_of(id).ok_or(KernelError::UnboundFVar { id }),
            ExprNode::Sort(level) => {
                // `Sort l : Sort (l+1)`.
                let succ = self.level_succ(level);
                Ok(self.sort(succ))
            }
            ExprNode::Const(name, levels) => self.infer_const(name, &levels),
            ExprNode::Proj(type_name, field_index, structure) => {
                self.infer_projection(type_name, field_index, structure, ctx)
            }
            ExprNode::Lit(Lit::Nat(_)) => self.infer_nat_literal(),
            ExprNode::Lit(Lit::Str(_)) => self.infer_string_literal(),
            ExprNode::App(..) => self.infer_app(e, ctx),
            ExprNode::Lam(name, dom, body, info) => {
                self.infer_lambda(e, name, dom, body, info, ctx)
            }
            ExprNode::Pi(name, dom, body, info) => self.infer_pi(name, dom, body, info, ctx),
            ExprNode::Let(name, ty, val, body) => self.infer_let(name, ty, val, body, ctx),
        }?;
        if closed {
            self.infer_closed_cache.insert(e, inferred);
        } else {
            ctx.remember_inferred(e, inferred);
            ctx.taint_infer_if_unbound_probed(mark, e);
        }
        Ok(inferred)
    }

    /// Infer `Proj(type_name, field_index, structure)` using Lean's checked
    /// single-constructor telescope algorithm.
    ///
    /// The projected value supplies the inductive's universe levels,
    /// parameters, and indices. Constructor parameters are instantiated from
    /// that type; each earlier dependent field is instantiated with a
    /// projection from the same value. This slice does not reduce projections
    /// of constructor applications (TL2.4) or add structure eta (TL2.5).
    fn infer_projection(
        &mut self,
        type_name: NameId,
        field_index: u32,
        structure: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<ExprId, KernelError> {
        let structure_type = self.infer_core(structure, ctx)?;
        let structure_type = self.whnf_core(structure_type, ctx);
        let data = self.projection_inference_data(type_name, field_index, structure_type)?;

        let mut cursor = self.infer_const(data.ctor_name, &data.levels)?;
        for &parameter in data.type_args.iter().take(data.num_params) {
            cursor = self.whnf_core(cursor, ctx);
            let ExprNode::Pi(_, _, body, _) = self.expr_node(cursor).clone() else {
                return Err(KernelError::MalformedProjectionConstructor {
                    name: type_name,
                    ctor: data.ctor_name,
                    field_index,
                });
            };
            cursor = self.instantiate(body, &[parameter]);
        }

        let structure_is_prop = self.type_expression_is_prop(structure_type, ctx)?;
        for previous_index in 0..field_index {
            cursor = self.whnf_core(cursor, ctx);
            let ExprNode::Pi(_, domain, body, _) = self.expr_node(cursor).clone() else {
                return Err(KernelError::MalformedProjectionConstructor {
                    name: type_name,
                    ctor: data.ctor_name,
                    field_index,
                });
            };
            if self.has_loose_bvars(body) {
                if structure_is_prop && !self.type_expression_is_prop(domain, ctx)? {
                    return Err(KernelError::ProjectionFromPropToType {
                        name: type_name,
                        field_index,
                    });
                }
                let previous = self.proj(type_name, previous_index, structure);
                cursor = self.instantiate(body, &[previous]);
            } else {
                cursor = body;
            }
        }

        cursor = self.whnf_core(cursor, ctx);
        let ExprNode::Pi(_, field_type, _, _) = self.expr_node(cursor).clone() else {
            return Err(KernelError::MalformedProjectionConstructor {
                name: type_name,
                ctor: data.ctor_name,
                field_index,
            });
        };
        if structure_is_prop && !self.type_expression_is_prop(field_type, ctx)? {
            return Err(KernelError::ProjectionFromPropToType {
                name: type_name,
                field_index,
            });
        }
        Ok(field_type)
    }

    /// Validate the projected type head, checked inductive metadata, complete
    /// parameter/index spine, sole constructor identity, and selected field
    /// bound before any constructor telescope is traversed.
    fn projection_inference_data(
        &self,
        type_name: NameId,
        field_index: u32,
        structure_type: ExprId,
    ) -> Result<ProjectionInferenceData, KernelError> {
        let (type_head, type_args) = self.unfold_apps(structure_type);
        let ExprNode::Const(inferred_name, levels) = self.expr_node(type_head).clone() else {
            return Err(KernelError::ProjectionTypeMismatch {
                expected: type_name,
                got: structure_type,
            });
        };
        if inferred_name != type_name {
            return Err(KernelError::ProjectionTypeMismatch {
                expected: type_name,
                got: structure_type,
            });
        }

        let (ctor_name, num_params, num_indices, constructor_count) = match self.env.get(type_name)
        {
            Some(Declaration::Inductive {
                num_params,
                num_indices,
                ctor_names,
                ..
            }) => (
                ctor_names.first().copied(),
                usize::from(*num_params),
                usize::from(*num_indices),
                ctor_names.len(),
            ),
            _ => {
                return Err(KernelError::ProjectionNotInductive { name: type_name });
            }
        };
        if constructor_count != 1 {
            return Err(KernelError::ProjectionConstructorCount {
                name: type_name,
                got: constructor_count,
            });
        }
        let Some(ctor_name) = ctor_name else {
            return Err(KernelError::ProjectionConstructorCount {
                name: type_name,
                got: constructor_count,
            });
        };
        let expected_arity = num_params + num_indices;
        if type_args.len() != expected_arity {
            return Err(KernelError::ProjectionArityMismatch {
                name: type_name,
                expected: expected_arity,
                got: type_args.len(),
            });
        }

        let field_count = match self.env.get(ctor_name) {
            Some(Declaration::Constructor {
                inductive,
                num_fields,
                ..
            }) if *inductive == type_name => *num_fields,
            _ => {
                return Err(KernelError::MalformedProjectionConstructor {
                    name: type_name,
                    ctor: ctor_name,
                    field_index,
                });
            }
        };
        if field_index >= u32::from(field_count) {
            return Err(KernelError::ProjectionFieldOutOfBounds {
                name: type_name,
                field_index,
                field_count,
            });
        }

        Ok(ProjectionInferenceData {
            ctor_name,
            num_params,
            levels,
            type_args,
        })
    }

    /// Whether a type expression is a proposition: its own inferred type
    /// WHNFs to `Sort 0` in the active local context.
    pub(crate) fn type_expression_is_prop(
        &mut self,
        expression: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<bool, KernelError> {
        let sort = self.infer_core(expression, ctx)?;
        let sort = self.whnf_core(sort, ctx);
        let ExprNode::Sort(level) = self.expr_node(sort) else {
            return Err(KernelError::NotASort { got: sort });
        };
        let level = *level;
        Ok(self.level_is_zero(level))
    }

    /// Infer a complete application spine in one dependent-telescope pass.
    ///
    /// The ordinary one-argument rule repeatedly instantiates the entire
    /// remaining function type for `f a₁ … aₙ`. That is semantically harmless
    /// but quadratic for large dependent recursor types. Here `cursor` retains
    /// the unopened telescope, each argument is checked against its domain with
    /// the preceding substitutions, and the result body is instantiated once.
    /// If reduction is required to expose another `Pi`, the accumulated
    /// substitutions are committed before WHNF and traversal resumes.
    fn infer_app(&mut self, e: ExprId, ctx: &mut LocalContext) -> Result<ExprId, KernelError> {
        let ExprNode::App(..) = self.expr_node(e) else {
            unreachable!("infer_app called on non-App")
        };
        let (head, args) = self.unfold_apps(e);
        let mut cursor = self.infer_core(head, ctx)?;
        let mut prior = Vec::with_capacity(args.len());
        let mut domains = Vec::with_capacity(args.len());

        for &argument in &args {
            if !matches!(self.expr_node(cursor), ExprNode::Pi(..)) {
                cursor = self.instantiate(cursor, &prior);
                prior.clear();
                cursor = self.whnf_core(cursor, ctx);
            }
            let ExprNode::Pi(_, domain, body, _) = self.expr_node(cursor).clone() else {
                return Err(KernelError::NotAPi { got: cursor });
            };
            let domain = self.instantiate(domain, &prior);
            domains.push(domain);
            prior.push(argument);
            cursor = body;
        }

        for (argument, domain) in args.iter().zip(domains) {
            self.check_core(*argument, domain, ctx)?;
        }
        Ok(self.instantiate(cursor, &prior))
    }

    /// `Lam(n, dom, body, bi)`: check `dom` is a type, open `body` under a
    /// fresh `FVar : dom`, infer the body type `B`, result
    /// `Pi(n, dom, abstract(B, fvar), bi)`.
    fn infer_lambda(
        &mut self,
        expression: ExprId,
        name: crate::name::NameId,
        dom: ExprId,
        body: ExprId,
        info: BinderInfo,
        ctx: &mut LocalContext,
    ) -> Result<ExprId, KernelError> {
        // The domain must be a type.
        self.infer_sort_of(dom, ctx)?;
        // Open the body.
        let scoped = ctx.scoped_fvar(expression);
        let fvar = scoped.unwrap_or_else(|| ctx.fresh_fvar());
        ctx.bump_fresh_above(fvar);
        let fv = self.fvar(fvar);
        ctx.push(LocalDecl {
            fvar,
            name,
            ty: dom,
            info,
        });
        let opened = if scoped.is_some() {
            body
        } else {
            self.instantiate(body, &[fv])
        };
        let b_ty = self.infer_core(opened, ctx);
        ctx.pop();
        let b_ty = b_ty?;
        // Re-abstract the inferred body type over the fvar and rebuild the Pi.
        let abstracted = self.abstract_fvars(b_ty, &[fvar]);
        Ok(self.pi(name, dom, abstracted, info))
    }

    /// `Pi(n, dom, body, bi)`: infer the domain sort `s1` and the body sort
    /// `s2` (under a fresh `FVar : dom`), result `Sort(IMax s1 s2)`.
    fn infer_pi(
        &mut self,
        name: crate::name::NameId,
        dom: ExprId,
        body: ExprId,
        info: BinderInfo,
        ctx: &mut LocalContext,
    ) -> Result<ExprId, KernelError> {
        let s1 = self.infer_sort_of(dom, ctx)?;
        let fvar = ctx.fresh_fvar();
        let fv = self.fvar(fvar);
        ctx.push(LocalDecl {
            fvar,
            name,
            ty: dom,
            info,
        });
        let opened = self.instantiate(body, &[fv]);
        let s2 = self.infer_sort_of(opened, ctx);
        ctx.pop();
        let s2 = s2?;
        let imax = self.level_imax(s1, s2);
        Ok(self.sort(imax))
    }

    /// `Let(n, ty, val, body)`: check `ty` is a type, check `infer(val)` def-eq
    /// `ty`, then infer `body` under a typed local and substitute `val` only in
    /// the resulting type.
    fn infer_let(
        &mut self,
        name: crate::name::NameId,
        ty: ExprId,
        val: ExprId,
        body: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<ExprId, KernelError> {
        // Gather one consecutive telescope so the remaining body is opened
        // exactly once. Repeatedly instantiating the tail of a 10k-let proof DAG
        // is quadratic and destroys the sharing the lets were introduced to keep.
        let mut telescope = vec![(name, ty, val)];
        let mut final_body = body;
        while let ExprNode::Let(next_name, next_ty, next_val, next_body) =
            self.expr_node(final_body).clone()
        {
            telescope.push((next_name, next_ty, next_val));
            final_body = next_body;
        }
        let mut fvar_ids = Vec::with_capacity(telescope.len());
        let mut fvar_values = Vec::with_capacity(telescope.len());
        let checked = (|| -> Result<ExprId, KernelError> {
            for &(name, raw_ty, raw_val) in &telescope {
                let opened_ty = self.instantiate(raw_ty, &fvar_values);
                self.infer_sort_of(opened_ty, ctx)?;
                let opened_val = self.instantiate(raw_val, &fvar_values);
                let val_ty = self.infer_core(opened_val, ctx)?;
                if !self.def_eq_core(val_ty, opened_ty, ctx) {
                    return Err(KernelError::TypeMismatch {
                        expected: opened_ty,
                        got: val_ty,
                    });
                }

                let fvar = ctx.fresh_fvar();
                let value = self.fvar(fvar);
                ctx.push_let(
                    LocalDecl {
                        fvar,
                        name,
                        ty: opened_ty,
                        info: BinderInfo::Default,
                    },
                    opened_val,
                );
                fvar_ids.push(fvar);
                fvar_values.push(value);
            }
            let opened = self.instantiate(final_body, &fvar_values);
            self.infer_core(opened, ctx)
        })();
        for _ in 0..fvar_ids.len() {
            ctx.pop();
        }
        let body_ty = checked?;
        let abstracted = self.abstract_fvars(body_ty, &fvar_ids);
        if abstracted == body_ty {
            return Ok(body_ty);
        }
        let mut closed_values = Vec::with_capacity(telescope.len());
        for &(_, _, raw_val) in &telescope {
            let closed_val = self.instantiate(raw_val, &closed_values);
            closed_values.push(closed_val);
        }
        Ok(self.instantiate(abstracted, &closed_values))
    }

    /// Infer the type of `Const(name, level_args)`: look up the declaration,
    /// check the universe-argument count matches the declaration's universe
    /// parameters, and return the declaration's type with `uparams ↦
    /// level_args` substituted (universe instantiation). Ported from nanoda's
    /// `infer_const`.
    fn infer_const(
        &mut self,
        name: crate::name::NameId,
        level_args: &[LevelId],
    ) -> Result<ExprId, KernelError> {
        let Some(decl) = self.env.get(name) else {
            return Err(KernelError::UnknownConst { name });
        };
        let uparams = decl.uparams().to_vec();
        let ty = decl.ty();
        if uparams.len() != level_args.len() {
            return Err(KernelError::UniverseArityMismatch {
                name,
                expected: uparams.len(),
                got: level_args.len(),
            });
        }
        let subst = Self::level_subst(&uparams, level_args);
        Ok(self.substitute_expr_levels(ty, &subst))
    }
}

#[cfg(test)]
mod tc_tests;
