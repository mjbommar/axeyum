//! Type-theory core: WHNF reduction, definitional equality, and type inference
//! for the environment-free fragment of the Lean kernel (ADR-0036, slice 2).
//!
//! This is the **trusted core**: a wrong type-checker wrongly accepts proofs.
//! The algorithm is ported faithfully from nanoda's `tc.rs` for the in-scope
//! fragment — `Sort`, `FVar` (locals), `App`, `Lam`, `Pi`, `Let`, `BVar` — and
//! it stops at the environment boundary with an explicit error rather than a
//! guess.
//!
//! ## Scope
//!
//! In scope: beta reduction, zeta/let reduction, the lazy structural
//! definitional-equality algorithm (quick check → WHNF → case split on
//! `Sort`/`Pi`/`Lam`/`App`), eta-expansion, proof irrelevance, and type
//! inference for the fragment above.
//!
//! **Deferred to the next slice** (and erroring cleanly if reached):
//! the global `Environment`/declarations, `Const` δ-unfolding, literal typing,
//! inductive/recursor (ι) reduction, and projection reduction. A `Const`
//! reaching inference returns [`KernelError::UnsupportedConst`]; a `Lit`
//! reaching inference returns [`KernelError::UnsupportedLit`]. Neither panics.
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

use crate::expr::{ExprId, ExprNode};
use crate::level::LevelId;
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
    /// A `Const` reached inference. The environment/declaration layer is
    /// deferred to the next slice (ADR-0036), so δ-unfolding and constant
    /// typing are unsupported here.
    UnsupportedConst {
        /// The constant's name id (interned in the owning kernel).
        name: crate::name::NameId,
    },
    /// A `Lit` reached inference. Literal typing needs the environment
    /// (`Nat`/`String` declarations), deferred to the next slice.
    UnsupportedLit,
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
    fn unfold_apps(&self, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
        let mut args = Vec::new();
        while let ExprNode::App(f, a) = self.expr_node(e) {
            args.push(*a);
            e = *f;
        }
        args.reverse();
        (e, args)
    }

    /// Re-apply `head` to `args` left-to-right.
    fn foldl_apps(&mut self, mut head: ExprId, args: impl IntoIterator<Item = ExprId>) -> ExprId {
        for a in args {
            head = self.app(head, a);
        }
        head
    }

    /// Weak head normal form for the in-scope fragment.
    ///
    /// Performs **beta** (`App(Lam, a)` → instantiate the lambda body) and
    /// **zeta/let** (`Let` → instantiate the value into the body) reduction,
    /// iterating to a weak-head-normal term. `Sort` levels are simplified to a
    /// canonical form (matching nanoda's `whnf_no_unfolding`). **Eta** is *not*
    /// performed here — it lives in [`Kernel::def_eq`], matching nanoda.
    ///
    /// There is no δ (no `Const` unfolding), ι (no recursor/inductive), or
    /// projection reduction in this slice; a head `Const`/`FVar`/`Sort`/`Pi`
    /// or `Lam` with no further arguments is already weak-head-normal.
    ///
    /// # Panics
    ///
    /// Does not panic on well-formed input. (`unwrap`s below are guarded by the
    /// surrounding pattern match.)
    #[must_use]
    pub fn whnf(&mut self, e: ExprId) -> ExprId {
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
                // A bare `Sort` is normal; simplify its level for canonicity.
                ExprNode::Sort(level) if args.is_empty() => {
                    let level = self.simplify(level);
                    return self.sort(level);
                }
                // All other heads are already weak-head-normal in this slice:
                // FVar, Const, Sort (applied — ill-typed but inert here), Pi,
                // BVar (loose — inert), Lit, and Lam with no args.
                _ => return cursor,
            }
        }
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

    /// The lazy structural algorithm (nanoda's `def_eq`/`def_eq_core` for the
    /// in-scope fragment): quick check, WHNF both sides, quick check again,
    /// then proof irrelevance, then case-split on the WHNF'd heads
    /// (`Sort`/binder congruence via the quick check, `FVar`, `App` spine,
    /// eta-expansion).
    fn def_eq_core(&mut self, x: ExprId, y: ExprId, ctx: &mut LocalContext) -> bool {
        if let Some(quick) = self.def_eq_quick(x, y, ctx) {
            return quick;
        }

        let x_n = self.whnf(x);
        let y_n = self.whnf(y);

        if let Some(quick) = self.def_eq_quick(x_n, y_n, ctx) {
            return quick;
        }

        if self.proof_irrel_eq(x_n, y_n, ctx) {
            return true;
        }

        // No δ here (no `Const`); the lazy-delta step of nanoda collapses to
        // the structural checks below for this fragment.
        if self.def_eq_fvar(x_n, y_n) {
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

    fn infer_core(&mut self, e: ExprId, ctx: &mut LocalContext) -> Result<ExprId, KernelError> {
        match self.expr_node(e).clone() {
            ExprNode::BVar(index) => Err(KernelError::LooseBVar { index }),
            ExprNode::FVar(id) => ctx.type_of(id).ok_or(KernelError::UnboundFVar { id }),
            ExprNode::Sort(level) => {
                // `Sort l : Sort (l+1)`.
                let succ = self.level_succ(level);
                Ok(self.sort(succ))
            }
            ExprNode::Const(name, _) => Err(KernelError::UnsupportedConst { name }),
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
}

#[cfg(test)]
mod tc_tests;
