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
//! **Deferred to a later slice** (and erroring cleanly if reached): literal
//! typing/reduction (`Lit` → [`KernelError::UnsupportedLit`]),
//! inductive/recursor (ι) reduction, structure projections, and `Quotient`
//! reduction. An unknown `Const` name returns [`KernelError::UnknownConst`].
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

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{ExprId, ExprNode};
use crate::level::LevelId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel};

/// An error from the environment-free type-checker.
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
    /// A `Lit` reached inference. Literal typing needs inductive `Nat`/`String`
    /// declarations and their reduction rules, deferred to a later slice.
    UnsupportedLit,
    /// A declaration with this name already exists in the environment;
    /// re-declaration is rejected.
    DeclarationExists {
        /// The name that was already declared.
        name: crate::name::NameId,
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
    /// A constructor field mentioned the inductive type being declared — a
    /// **recursive** constructor. Recursive inductives (the induction
    /// hypothesis, positivity checking) are deferred to a later slice; this
    /// slice supports only non-recursive inductives.
    RecursiveInductiveNotSupported {
        /// The inductive whose constructor was recursive.
        inductive: crate::name::NameId,
        /// The recursive constructor.
        ctor: crate::name::NameId,
    },
    /// A constructor's type used a `Pi` whose result was not an application of
    /// the parent inductive's constant head, or was otherwise malformed for the
    /// non-parametric scope (e.g. a parametric/indexed result).
    MalformedConstructorType {
        /// The constructor whose type was malformed.
        ctor: crate::name::NameId,
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

    /// Push a local declaration onto the stack.
    pub fn push(&mut self, decl: LocalDecl) {
        self.decls.push(decl);
    }

    /// Pop the most recently pushed local declaration (LIFO).
    pub fn pop(&mut self) -> Option<LocalDecl> {
        self.decls.pop()
    }

    /// Look up the type recorded for free variable `id`, if any.
    #[must_use]
    pub fn type_of(&self, id: u64) -> Option<ExprId> {
        self.decls.iter().rev().find(|d| d.fvar == id).map(|d| d.ty)
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

    /// Weak head normal form **without** δ-unfolding: beta, zeta/let, and
    /// `Sort`-level simplification only. Ported from nanoda's
    /// `whnf_no_unfolding`. A head `Const`/`FVar`/`Sort`/`Pi` or `Lam` with no
    /// further arguments is already weak-head-normal here.
    fn whnf_no_unfolding(&mut self, e: ExprId) -> ExprId {
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
                // ι: a recursor `Const(I.rec, _)` applied to its premises and a
                // constructor-headed major reduces to the matching minor applied
                // to the constructor's fields (ADR-0036, slice 4).
                ExprNode::Const(..) => match self.reduce_rec(cursor) {
                    Some(reduced) => cursor = reduced,
                    None => return cursor,
                },
                // A bare `Sort` is normal; simplify its level for canonicity.
                ExprNode::Sort(level) if args.is_empty() => {
                    let level = self.simplify(level);
                    return self.sort(level);
                }
                // All other heads are already weak-head-normal here: FVar,
                // Const, Sort (applied — ill-typed but inert), Pi, BVar (loose —
                // inert), Lit, and Lam with no args.
                _ => return cursor,
            }
        }
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
    /// nanoda's `get_declar_val`). There is no ι (recursor/inductive) or
    /// projection reduction in this slice.
    ///
    /// # Panics
    ///
    /// Does not panic on well-formed input.
    #[must_use]
    pub fn whnf(&mut self, e: ExprId) -> ExprId {
        let mut cursor = e;
        loop {
            let whnfd = self.whnf_no_unfolding(cursor);
            match self.unfold_def(whnfd) {
                Some(next) => cursor = next,
                None => return whnfd,
            }
        }
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
    fn delta(&mut self, e: ExprId) -> ExprId {
        let unfolded = self
            .unfold_def(e)
            .expect("delta called on a non-unfoldable expression");
        self.whnf_no_unfolding(unfolded)
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
    /// [`KernelError::DeclarationTypeNotASort`] if the type is not a type,
    /// [`KernelError::DeclarationValueMismatch`] if a value's type does not
    /// match the declared type, or any [`KernelError`] surfaced while inferring
    /// the type or value (e.g. [`KernelError::UnknownConst`] for a dangling
    /// reference).
    pub fn add_declaration(&mut self, decl: Declaration) -> Result<(), KernelError> {
        let name = decl.name();
        if self.env.contains(name) {
            return Err(KernelError::DeclarationExists { name });
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

        self.env.insert_unchecked(decl);
        Ok(())
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
        let y_ty = self.whnf(y_ty);
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
        let sort = self.whnf(sort);
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
            let r1 = self.get_applied_def(x);
            let r2 = self.get_applied_def(y);
            match (r1, r2) {
                (None, None) => return DeltaResult::Exhausted(x, y),
                (Some(_), None) => x = self.delta(x),
                (None, Some(_)) => y = self.delta(y),
                (Some((_, l_hint)), Some((_, r_hint))) if l_hint.is_lt(r_hint) => {
                    y = self.delta(y);
                }
                (Some((_, l_hint)), Some((_, r_hint))) if r_hint.is_lt(l_hint) => {
                    x = self.delta(x);
                }
                (Some((x_name, l_hint)), Some((y_name, r_hint))) => {
                    if let Some(r) =
                        self.try_eq_const_app(x, x_name, l_hint, y, y_name, r_hint, ctx)
                    {
                        return DeltaResult::FoundEqResult(r);
                    }
                    x = self.delta(x);
                    y = self.delta(y);
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
    /// spine, eta-expansion) on the delta-exhausted heads.
    fn def_eq_core(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        if let Some(quick) = self.def_eq_quick(x, y, ctx) {
            return quick;
        }

        // WHNF without δ — δ is handled lazily by `lazy_delta_step` below so
        // that we unfold only as far as needed (matching nanoda).
        let x_n = self.whnf_no_unfolding(x);
        let y_n = self.whnf_no_unfolding(y);

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
                if self.def_eq_app(x_n, y_n, ctx) {
                    return true;
                }
                if self.try_eta_expansion(x_n, y_n, ctx) {
                    return true;
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

// ---------------------------------------------------------------------------
// Type inference
// ---------------------------------------------------------------------------

impl Kernel {
    /// Infer the type of `e` for the environment-free fragment, in a checking
    /// mode that validates as it goes.
    ///
    /// Allocates a fresh [`LocalContext`]; use [`Kernel::infer_in`] to share an
    /// existing one.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError`] for ill-typed or out-of-scope input: a non-`Pi`
    /// applied as a function ([`KernelError::NotAPi`]), a binder domain that is
    /// not a type ([`KernelError::NotASort`]), an argument or `let`-value type
    /// mismatch ([`KernelError::TypeMismatch`]), a loose `BVar`
    /// ([`KernelError::LooseBVar`]), an unbound `FVar`
    /// ([`KernelError::UnboundFVar`]), a `Const`
    /// ([`KernelError::UnsupportedConst`]), or a `Lit`
    /// ([`KernelError::UnsupportedLit`]).
    pub fn infer(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
        let mut ctx = LocalContext::new();
        self.infer_core(e, &mut ctx)
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
        let ty = self.whnf(ty);
        match self.expr_node(ty) {
            ExprNode::Sort(level) => Ok(*level),
            _ => Err(KernelError::NotASort { got: ty }),
        }
    }

    pub(crate) fn infer_core(
        &mut self,
        e: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<ExprId, KernelError> {
        match self.expr_node(e).clone() {
            ExprNode::BVar(index) => Err(KernelError::LooseBVar { index }),
            ExprNode::FVar(id) => ctx.type_of(id).ok_or(KernelError::UnboundFVar { id }),
            ExprNode::Sort(level) => {
                // `Sort l : Sort (l+1)`.
                let succ = self.level_succ(level);
                Ok(self.sort(succ))
            }
            ExprNode::Const(name, levels) => self.infer_const(name, &levels),
            ExprNode::Lit(_) => Err(KernelError::UnsupportedLit),
            ExprNode::App(..) => self.infer_app(e, ctx),
            ExprNode::Lam(name, dom, body, info) => self.infer_lambda(name, dom, body, info, ctx),
            ExprNode::Pi(name, dom, body, info) => self.infer_pi(name, dom, body, info, ctx),
            ExprNode::Let(name, ty, val, body) => self.infer_let(name, ty, val, body, ctx),
        }
    }

    /// `App(f, a)`: infer `f`, WHNF to a `Pi(_, dom, body, _)`, require
    /// `infer(a)` def-eq `dom`, result `instantiate(body, [a])`.
    fn infer_app(&mut self, e: ExprId, ctx: &mut LocalContext) -> Result<ExprId, KernelError> {
        let ExprNode::App(f, a) = self.expr_node(e).clone() else {
            unreachable!("infer_app called on non-App")
        };
        let f_ty = self.infer_core(f, ctx)?;
        let f_ty = self.whnf(f_ty);
        let ExprNode::Pi(_, dom, body, _) = self.expr_node(f_ty).clone() else {
            return Err(KernelError::NotAPi { got: f_ty });
        };
        let a_ty = self.infer_core(a, ctx)?;
        if !self.def_eq_core(a_ty, dom, ctx) {
            return Err(KernelError::TypeMismatch {
                expected: dom,
                got: a_ty,
            });
        }
        Ok(self.instantiate(body, &[a]))
    }

    /// `Lam(n, dom, body, bi)`: check `dom` is a type, open `body` under a
    /// fresh `FVar : dom`, infer the body type `B`, result
    /// `Pi(n, dom, abstract(B, fvar), bi)`.
    fn infer_lambda(
        &mut self,
        name: crate::name::NameId,
        dom: ExprId,
        body: ExprId,
        info: BinderInfo,
        ctx: &mut LocalContext,
    ) -> Result<ExprId, KernelError> {
        // The domain must be a type.
        self.infer_sort_of(dom, ctx)?;
        // Open the body.
        let fvar = ctx.fresh_fvar();
        let fv = self.fvar(fvar);
        ctx.push(LocalDecl {
            fvar,
            name,
            ty: dom,
            info,
        });
        let opened = self.instantiate(body, &[fv]);
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
    /// `ty`, then infer `body` with `val` instantiated (nanoda's `infer_let`).
    fn infer_let(
        &mut self,
        _name: crate::name::NameId,
        ty: ExprId,
        val: ExprId,
        body: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<ExprId, KernelError> {
        // The annotation must be a type.
        self.infer_sort_of(ty, ctx)?;
        // The value's type must match the annotation.
        let val_ty = self.infer_core(val, ctx)?;
        if !self.def_eq_core(val_ty, ty, ctx) {
            return Err(KernelError::TypeMismatch {
                expected: ty,
                got: val_ty,
            });
        }
        // Substitute the value into the body and infer that (zeta), matching
        // nanoda: `let` is reduced rather than opened as a local.
        let instd = self.instantiate(body, &[val]);
        self.infer_core(instd, ctx)
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
