//! The inductive layer (ADR-0036, slice 6): the trusted [`Kernel::add_inductive`]
//! admission gate, recursor generation (with induction hypotheses and
//! parameters), and ι-reduction in WHNF.
//!
//! ## Scope — parametric, direct-recursive inductives (still non-indexed)
//!
//! This slice supports inductive types that are **parametric** (`m` leading
//! parameter binders fixed across the family) and **non-indexed**, whose
//! constructors may have **direct recursive fields**. An inductive
//! `I : Π (p_1 … p_m), Sort u` has `m` leading *parameter* binders and then,
//! with **`num_indices` = 0**, the remainder must be exactly a `Sort` (any
//! binder between the parameters and the `Sort` is an *index*, which is deferred
//! and rejected as [`KernelError::IndicesNotSupported`]).
//!
//! Each constructor is `c : Π (p_1…p_m) (fields…), I p_1…p_m`: it re-binds the
//! **same** `m` parameters (whose types must be def-eq to the inductive's), then
//! its fields, and its result is exactly the inductive applied to those `m`
//! parameter binders, in order. A field is a **direct recursive field** iff its
//! type is exactly `I p_1…p_m` (the inductive applied to the parameters); any
//! other occurrence of `I` is rejected. This unlocks `List α`, `Option α`,
//! `Prod α β`, `Sum α β` (on top of slice-5 `Nat`, binary trees, and the
//! slice-4 enums/structures, all of which are now `num_params = 0`).
//!
//! Direct recursive fields are trivially strictly-positive, so no positivity
//! analysis is required here.
//!
//! **Deferred** (and rejected explicitly, never guessed): **indices**
//! (`Eq`/`Vector` — `num_indices` > 0, reported as
//! [`KernelError::IndicesNotSupported`]), **higher-order / reflexive** recursive
//! fields (`(A → I p…)` — a field whose type is a `Pi` ending in `I`, reported as
//! [`KernelError::ReflexiveOrNestedNotSupported`]), nested and mutual
//! inductives, and the `Prop`-subsingleton large-elimination subtleties. The
//! motive is always allowed to eliminate into an arbitrary `Sort v` here.
//!
//! ## What is built
//!
//! For a checked parametric inductive `I` with parameters `p_1 … p_m` and
//! constructors `c_1 … c_n`, where `c_i` has fields `f_1 … f_k` of which
//! `f_{j1} … f_{jr}` are recursive:
//!
//! - `I.rec : Π (p_1…p_m) {motive : (I p_1…p_m) → Sort v}
//!            (m_1 : Π fields_1 (ih…), motive (c_1 p_1…p_m fields_1)) …
//!            (m_n : …)
//!            (major : I p_1…p_m), motive major`
//!   where the parameters come **before** the motive (Lean convention), and each
//!   minor premise `m_i` adds, after its `k` field binders, **one
//!   induction-hypothesis binder `ih_j : motive f_j` per recursive field `f_j`**
//!   (in field order). The parameters are threaded into both the constructor
//!   application `c_i p_1…p_m fields…` and the recursive `motive` applications.
//! - one [`RecRule`] per constructor, with
//!   `value = λ params motive m_1 … m_n (fields_i…),
//!            m_i fields_i… (I.rec params motive m… f_j)…`
//!   — the ι-RHS applies the minor to the fields and then to one recursive call
//!   `I.rec params motive minors… f_j` per recursive field `f_j` (the
//!   parameters are threaded into each recursive call).
//!
//! The generated recursor's type is itself `infer`-checked (a self-check):
//! a wrong recursor (e.g. a mis-indexed induction hypothesis or a mis-threaded
//! parameter) would wrongly accept proofs, so it is verified rather than
//! trusted.

use crate::env::{Declaration, RecRule};
use crate::expr::{ExprId, ExprNode};
use crate::name::NameId;
use crate::tc::{KernelError, LocalContext, LocalDecl};
use crate::{BinderInfo, Kernel};

impl Kernel {
    /// Type-check and admit an inductive type together with its constructors —
    /// the **trusted inductive gate** (ADR-0036, slice 6).
    ///
    /// `num_params` is the number of leading binders of `ty` that are
    /// **parameters** (fixed across the family); the caller declares this,
    /// mirroring Lean's export. After opening those `m = num_params` parameter
    /// binders the remainder of `ty` must WHNF to a `Sort` (no indices). `ctors`
    /// pairs each constructor's name with its type, in declaration order. On
    /// success this registers the [`Declaration::Inductive`], one
    /// [`Declaration::Constructor`] per constructor, and the generated
    /// [`Declaration::Recursor`] (whose type is `infer`-checked).
    ///
    /// Admission requires:
    ///
    /// 1. no declaration with the inductive's (or any constructor's) name exists;
    /// 2. `ty` opens `num_params` leading parameter binders and then WHNFs to a
    ///    `Sort` (a parametric, non-indexed inductive) — a remaining `Pi` is an
    ///    index and is rejected;
    /// 3. each constructor's type re-binds the **same** `num_params` parameters
    ///    (their types def-eq to the inductive's), then a telescope of fields
    ///    whose types type-check and whose result head is exactly the inductive
    ///    applied to those parameters in order. A field type may be non-recursive
    ///    (it does not mention `I`) or a **direct recursive field** (its type is
    ///    exactly `I p_1…p_m`). Any other occurrence of `I` is rejected.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError::DeclarationExists`] for a duplicate name,
    /// [`KernelError::InductiveTypeNotASort`] if `ty`'s parameter-stripped tail
    /// is not a `Sort` for a non-`Pi` head, [`KernelError::IndicesNotSupported`]
    /// if a binder remains between the parameters and the `Sort` (an index),
    /// [`KernelError::ReflexiveOrNestedNotSupported`] for a reflexive/nested
    /// recursive field, [`KernelError::RecursiveInductiveNotSupported`] for an
    /// ill-shaped recursive self-reference, [`KernelError::ConstructorResultMismatch`] /
    /// [`KernelError::MalformedConstructorType`] for a wrong/ill-formed
    /// constructor result or parameter prefix, or any [`KernelError`] surfaced
    /// while inferring a field type or the generated recursor type.
    ///
    /// # Panics
    ///
    /// Does not panic on well-formed or ill-formed input; all rejections are
    /// returned as [`KernelError`]s.
    pub fn add_inductive(
        &mut self,
        name: NameId,
        uparams: &[NameId],
        num_params: usize,
        ty: ExprId,
        ctors: &[(NameId, ExprId)],
    ) -> Result<(), KernelError> {
        // (1) Names must be fresh (the inductive, the constructors, and the
        // to-be-generated recursor).
        if self.env.contains(name) {
            return Err(KernelError::DeclarationExists { name });
        }
        for (cn, _) in ctors {
            if self.env.contains(*cn) {
                return Err(KernelError::DeclarationExists { name: *cn });
            }
        }
        let rec_str = "rec";
        let rec_name = self.name_str(name, rec_str);
        if self.env.contains(rec_name) {
            return Err(KernelError::DeclarationExists { name: rec_name });
        }

        // (2) The inductive's type must itself type-check (its type infers to a
        // Sort-of-a-Sort) and, after opening `num_params` parameter binders,
        // WHNF to a `Sort` (parametric, non-indexed). A remaining `Pi` is an
        // index (deferred); any other head is ill-typed.
        let mut ctx = LocalContext::new();
        let ty_ty = self.infer_core(ty, &mut ctx)?;
        let ty_ty = self.whnf(ty_ty);
        if !matches!(self.expr_node(ty_ty), ExprNode::Sort(_)) {
            return Err(KernelError::InductiveTypeNotASort { got: ty_ty });
        }
        // Open the parameter telescope into fresh fvars, instantiating each
        // subsequent binder. These param locals are the canonical parameters of
        // the family, threaded everywhere below.
        let mut params: Vec<LocalDecl> = Vec::with_capacity(num_params);
        let mut cursor = self.whnf(ty);
        for _ in 0..num_params {
            let ExprNode::Pi(bname, dom, body, info) = self.expr_node(cursor).clone() else {
                // Fewer leading Pis than declared parameters: the type cannot
                // bind that many parameters.
                return Err(KernelError::InductiveTypeNotASort { got: cursor });
            };
            let fvar = ctx.fresh_fvar();
            let decl = LocalDecl {
                fvar,
                name: bname,
                ty: dom,
                info,
            };
            ctx.push(decl);
            params.push(decl);
            let fv = self.fvar(fvar);
            cursor = self.instantiate(body, &[fv]);
            cursor = self.whnf(cursor);
        }
        // The remainder must be exactly a `Sort` (num_indices = 0). A remaining
        // `Pi` is an index (deferred); any other head is ill-typed.
        if !matches!(self.expr_node(cursor), ExprNode::Sort(_)) {
            if matches!(self.expr_node(cursor), ExprNode::Pi(..)) {
                return Err(KernelError::IndicesNotSupported { inductive: name });
            }
            return Err(KernelError::InductiveTypeNotASort { got: cursor });
        }

        // The inductive constant `Const(I, uparams-as-levels)`, used as the
        // applied result head and for the major premise's type.
        let ind_const = self.mk_ind_const(name, uparams);

        // (3) Check each constructor and collect its opened field locals.
        //
        // We register the Inductive declaration FIRST (so field types and the
        // recursor type, which reference `Const(I, …)`, resolve), then validate
        // every constructor; if a constructor fails we roll the inductive back.
        let ctor_names: Vec<NameId> = ctors.iter().map(|(n, _)| *n).collect();
        self.env.insert_unchecked(Declaration::Inductive {
            name,
            uparams: uparams.to_vec(),
            ty,
            ctor_names,
        });

        // The parameter types (the inductive's declared parameter domains), used
        // to check each constructor re-binds parameters of the same types.
        let param_types: Vec<ExprId> = params.iter().map(|p| p.ty).collect();

        let mut checked: Vec<CheckedCtor> = Vec::with_capacity(ctors.len());
        for (idx, (cn, cty)) in ctors.iter().copied().enumerate() {
            match self.check_ctor(name, ind_const, num_params, &param_types, cn, cty) {
                Ok((fields, recursive_fields)) => checked.push(CheckedCtor {
                    name: cn,
                    ty: cty,
                    idx: u16::try_from(idx).expect("ctor count fits u16"),
                    fields,
                    recursive_fields,
                }),
                Err(e) => {
                    // Roll back the inductive so the environment is unchanged.
                    self.env.remove_unchecked(name);
                    return Err(e);
                }
            }
        }

        // Register the constructors. `num_fields` excludes the parameters (the
        // ι-rule and recursor strip the params before the fields).
        for c in &checked {
            self.env.insert_unchecked(Declaration::Constructor {
                name: c.name,
                uparams: uparams.to_vec(),
                ty: c.ty,
                inductive: name,
                idx: c.idx,
                num_fields: u16::try_from(c.fields.len()).expect("field count fits u16"),
            });
        }

        // Generate and register the recursor (and its rec rules). Its type is
        // infer-checked here (the self-check); on failure, roll everything back.
        match self.mk_recursor(rec_name, uparams, num_params, ty, ind_const, &checked) {
            Ok(rec_decl) => {
                self.env.insert_unchecked(rec_decl);
                Ok(())
            }
            Err(e) => {
                self.env.remove_unchecked(name);
                for c in &checked {
                    self.env.remove_unchecked(c.name);
                }
                Err(e)
            }
        }
    }

    /// Build `Const(I, [Param(u) for u in uparams])`.
    fn mk_ind_const(&mut self, name: NameId, uparams: &[NameId]) -> ExprId {
        let levels = uparams.iter().map(|&u| self.level_param(u)).collect();
        self.const_(name, levels)
    }

    /// Check one constructor of a parametric inductive: open its leading
    /// parameter telescope (the **same** `num_params` parameters as the
    /// inductive, whose declared types must be def-eq to `param_types`), then its
    /// field telescope into fresh locals, classifying each field as
    /// non-recursive or a **direct recursive field** (its type is exactly
    /// `I p_1…p_m`, the inductive applied to those parameter fvars in order), and
    /// require the result head to be exactly `I p_1…p_m`. Returns the opened
    /// **field** locals (outer-to-inner; the parameters are *not* included),
    /// together with the field positions that are recursive (ascending).
    ///
    /// Any occurrence of `I` in a field type that is *not* the direct field
    /// `I p_1…p_m` is rejected: a `Pi` ending in `I` (reflexive/higher-order) ⇒
    /// [`KernelError::ReflexiveOrNestedNotSupported`]; a self-reference applied
    /// to the wrong arguments ⇒ [`KernelError::RecursiveInductiveNotSupported`];
    /// any deeper occurrence ⇒ [`KernelError::ReflexiveOrNestedNotSupported`].
    fn check_ctor(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
        num_params: usize,
        param_types: &[ExprId],
        ctor_name: NameId,
        ctor_ty: ExprId,
    ) -> Result<(Vec<LocalDecl>, Vec<usize>), KernelError> {
        let mut ctx = LocalContext::new();
        // The constructor's type must itself type-check (to a Sort).
        let cty_ty = self.infer_core(ctor_ty, &mut ctx)?;
        let cty_ty = self.whnf(cty_ty);
        if !matches!(self.expr_node(cty_ty), ExprNode::Sort(_)) {
            return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
        }

        let mut cursor = self.whnf(ctor_ty);

        // Open the `num_params` leading parameter binders. Their declared types
        // must be def-eq to the inductive's parameter types (so the constructor
        // re-binds the SAME parameters). The opened fvars are the parameters
        // `p_1…p_m` used as the expected recursive-field and result head args.
        let mut param_locals: Vec<LocalDecl> = Vec::with_capacity(num_params);
        for &pty in param_types.iter().take(num_params) {
            let ExprNode::Pi(bname, dom, body, info) = self.expr_node(cursor).clone() else {
                // Fewer leading binders than parameters ⇒ the constructor does
                // not re-bind all parameters.
                return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
            };
            if !self.def_eq(dom, pty) {
                return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
            }
            let fvar = ctx.fresh_fvar();
            let decl = LocalDecl {
                fvar,
                name: bname,
                ty: dom,
                info,
            };
            ctx.push(decl);
            param_locals.push(decl);
            let fv = self.fvar(fvar);
            cursor = self.instantiate(body, &[fv]);
            cursor = self.whnf(cursor);
        }

        // The expected applied-inductive head `I p_1…p_m` (the inductive applied
        // to the constructor's own parameter fvars, in order). This is both the
        // shape of a direct recursive field and the required telescope result.
        let ind_applied = {
            let mut app = ind_const;
            for p in &param_locals {
                let fv = self.fvar(p.fvar);
                app = self.app(app, fv);
            }
            app
        };

        let mut fields: Vec<LocalDecl> = Vec::new();
        let mut recursive_fields: Vec<usize> = Vec::new();
        while let ExprNode::Pi(bname, dom, body, info) = self.expr_node(cursor).clone() {
            // Classify the field's occurrence of `I`, if any. A direct recursive
            // field (`dom == I p_1…p_m`) is admitted and recorded; everything
            // else mentioning `I` is rejected with a precise error.
            if self.mentions_const(dom, ind_name) {
                if dom == ind_applied {
                    // Direct recursive field: exactly `I p_1…p_m`.
                    recursive_fields.push(fields.len());
                } else {
                    return Err(
                        self.classify_bad_recursive_field(ind_name, ind_const, ctor_name, dom)
                    );
                }
            }
            let fvar = ctx.fresh_fvar();
            let decl = LocalDecl {
                fvar,
                name: bname,
                ty: dom,
                info,
            };
            ctx.push(decl);
            fields.push(decl);
            let fv = self.fvar(fvar);
            cursor = self.instantiate(body, &[fv]);
            cursor = self.whnf(cursor);
        }

        // The telescope must end exactly in the inductive applied to the
        // constructor's parameters: `I p_1…p_m`.
        if cursor != ind_applied {
            // Distinguish "wrong head inductive" from "wrong params/indices".
            let (head, _args) = self.unfold_apps(cursor);
            if let ExprNode::Const(n, _) = self.expr_node(head) {
                if *n == ind_name {
                    // Right inductive, but applied to the wrong args (wrong
                    // params, or indices) ⇒ result mismatch / malformed.
                    return Err(KernelError::ConstructorResultMismatch {
                        expected: ind_name,
                        ctor: ctor_name,
                    });
                }
                return Err(KernelError::ConstructorResultMismatch {
                    expected: ind_name,
                    ctor: ctor_name,
                });
            }
            return Err(KernelError::ConstructorResultMismatch {
                expected: ind_name,
                ctor: ctor_name,
            });
        }
        Ok((fields, recursive_fields))
    }

    /// Classify a field type `dom` that mentions `I` but is **not** the direct
    /// field `I p_1…p_m`, into the appropriate deferred-error.
    ///
    /// - a `Pi` whose telescope ends in `I` (a reflexive/higher-order field,
    ///   e.g. `(A → I p…)`) ⇒ [`KernelError::ReflexiveOrNestedNotSupported`];
    /// - a self-reference applied to the **wrong** arguments (`I a…` where the
    ///   args are not the parameters) ⇒
    ///   [`KernelError::RecursiveInductiveNotSupported`];
    /// - any other occurrence (nested under another head, etc.)
    ///   ⇒ [`KernelError::ReflexiveOrNestedNotSupported`].
    fn classify_bad_recursive_field(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
        ctor_name: NameId,
        dom: ExprId,
    ) -> KernelError {
        // A `Pi`-headed field that ultimately yields `I` is reflexive/nested.
        if matches!(self.expr_node(dom), ExprNode::Pi(..)) {
            return KernelError::ReflexiveOrNestedNotSupported {
                inductive: ind_name,
                ctor: ctor_name,
            };
        }
        // `I` applied to arguments (`Const(I, _) a…`) whose head is the
        // inductive constant but which is not the canonical `I p_1…p_m` is a
        // mis-applied recursive self-reference (wrong params/indices).
        let (head, args) = self.unfold_apps(dom);
        if !args.is_empty() && head == ind_const {
            return KernelError::RecursiveInductiveNotSupported {
                inductive: ind_name,
                ctor: ctor_name,
            };
        }
        // Anything else mentioning `I` (nested under a different head, etc.).
        KernelError::ReflexiveOrNestedNotSupported {
            inductive: ind_name,
            ctor: ctor_name,
        }
    }

    /// Whether the constant named `target` occurs anywhere in `e` (used for the
    /// non-recursive field restriction). A purely structural search; no
    /// reduction.
    fn mentions_const(&self, e: ExprId, target: NameId) -> bool {
        match self.expr_node(e).clone() {
            ExprNode::Const(n, _) => n == target,
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => false,
            ExprNode::App(f, a) => self.mentions_const(f, target) || self.mentions_const(a, target),
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                self.mentions_const(ty, target) || self.mentions_const(body, target)
            }
            ExprNode::Let(_, ty, val, body) => {
                self.mentions_const(ty, target)
                    || self.mentions_const(val, target)
                    || self.mentions_const(body, target)
            }
        }
    }
}

/// A constructor after checking: its opened field locals plus identity data.
struct CheckedCtor {
    name: NameId,
    ty: ExprId,
    idx: u16,
    /// The opened **field** locals (outer-to-inner), each carrying name/type/info.
    /// The leading parameters are *not* included here.
    fields: Vec<LocalDecl>,
    /// The 0-based field positions (within `fields`, parameters excluded) that
    /// are **direct recursive fields** (type exactly `I p_1…p_m`), ascending.
    /// One induction hypothesis (in the recursor's minor premise) and one
    /// recursive call (in the ι-rule) is generated per entry, in this order.
    recursive_fields: Vec<usize>,
}

// ---------------------------------------------------------------------------
// Telescope abstraction helpers (port of nanoda's abstr_pi/abstr_lambda)
// ---------------------------------------------------------------------------

impl Kernel {
    /// Build `Π locals, body`, abstracting the `locals` (outer-to-inner) out of
    /// `body`. Each local's recorded type may itself reference outer locals;
    /// those are abstracted as the wrap proceeds outward. Mirrors nanoda's
    /// `abstr_pi_telescope`.
    fn abstr_pi_telescope(&mut self, locals: &[LocalDecl], body: ExprId) -> ExprId {
        let mut acc = body;
        for local in locals.iter().rev() {
            acc = self.abstract_fvars(acc, &[local.fvar]);
            acc = self.pi(local.name, local.ty, acc, local.info);
        }
        acc
    }

    /// Build `λ locals, body` analogously to [`Kernel::abstr_pi_telescope`].
    fn abstr_lambda_telescope(&mut self, locals: &[LocalDecl], body: ExprId) -> ExprId {
        let mut acc = body;
        for local in locals.iter().rev() {
            acc = self.abstract_fvars(acc, &[local.fvar]);
            acc = self.lam(local.name, local.ty, acc, local.info);
        }
        acc
    }
}

// ---------------------------------------------------------------------------
// Recursor generation
// ---------------------------------------------------------------------------

impl Kernel {
    /// Generate the recursor declaration (type + rec rules) for a checked
    /// parametric inductive. The recursor's type is `infer`-checked before it is
    /// returned (the soundness self-check).
    ///
    /// The recursor binds, outer-to-inner: the parameters `p_1…p_m`, the implicit
    /// motive `{motive : (I p_1…p_m) → Sort v}`, the minor premises, and the
    /// major `(major : I p_1…p_m)`, yielding `motive major`. The parameters are
    /// threaded into every constructor application and recursive `motive`
    /// application.
    #[allow(clippy::too_many_lines, clippy::too_many_arguments)]
    fn mk_recursor(
        &mut self,
        rec_name: NameId,
        uparams: &[NameId],
        num_params: usize,
        ind_ty: ExprId,
        ind_const: ExprId,
        ctors: &[CheckedCtor],
    ) -> Result<Declaration, KernelError> {
        // A fresh elimination universe parameter `v`, distinct from the
        // inductive's uparams. The recursor's uparams are `[v] ++ uparams`.
        let elim_param = self.fresh_elim_param(uparams);
        let elim_level = self.level_param(elim_param);
        let elim_sort = self.sort(elim_level);
        let mut rec_uparams = Vec::with_capacity(uparams.len() + 1);
        rec_uparams.push(elim_param);
        rec_uparams.extend_from_slice(uparams);

        // We work in one shared local context: params, then motive, then the
        // minors. The fields for each constructor live in nested contexts during
        // minor and rec-rule construction.
        let mut ctx = LocalContext::new();

        // Open the parameter locals `p_1…p_m` (the recursor's leading binders)
        // from the inductive's declared type telescope, with fresh fvars shared
        // across the whole recursor.
        let params = self.open_rec_params(&mut ctx, num_params, ind_ty);

        // The applied inductive `I p_1…p_m` (parameters threaded), used for the
        // motive's domain, the major's type, and constructor/motive results.
        let ind_applied = {
            let mut app = ind_const;
            for p in &params {
                let fv = self.fvar(p.fvar);
                app = self.app(app, fv);
            }
            app
        };

        // motive : (I p_1…p_m) → Sort v   (implicit). No indices ⇒ a plain arrow.
        let motive_ty = {
            // Π (_ : I p…), Sort v   — the bound var is unused, so the body is a
            // closed `Sort v` (no BVar).
            let anon = self.anon();
            self.pi(anon, ind_applied, elim_sort, BinderInfo::Default)
        };
        let motive_fvar = ctx.fresh_fvar();
        let motive_name = self.name_str_anon("motive");
        let motive_decl = LocalDecl {
            fvar: motive_fvar,
            name: motive_name,
            ty: motive_ty,
            info: BinderInfo::Implicit,
        };
        ctx.push(motive_decl);
        let motive = self.fvar(motive_fvar);

        // For each constructor, build the minor premise local and remember its
        // opened fields (re-opened here with fresh fvars in this context).
        let mut minors: Vec<LocalDecl> = Vec::with_capacity(ctors.len());
        // Per-ctor: the field locals opened for the minor (used in rec rules).
        let mut ctor_fields: Vec<Vec<LocalDecl>> = Vec::with_capacity(ctors.len());
        for c in ctors {
            let fields = self.open_ctor_fields(&mut ctx, num_params, &params, c);
            // c_i p_1…p_m fields…  :  I p_1…p_m
            let ctor_app = {
                let head = self.mk_ind_const_for_ctor(c.name, uparams);
                let mut app = head;
                for p in &params {
                    let fv = self.fvar(p.fvar);
                    app = self.app(app, fv);
                }
                for f in &fields {
                    let fv = self.fvar(f.fvar);
                    app = self.app(app, fv);
                }
                app
            };
            // motive (c_i p_1…p_m fields…)
            let motive_app = self.app(motive, ctor_app);
            // One induction-hypothesis binder `ih_j : motive f_j` per recursive
            // field `f_j`, in field order, opened *after* the field binders so
            // each IH's type references the already-bound field fvar.
            let ih_locals = self.open_ih_locals(&mut ctx, motive, &fields, &c.recursive_fields);
            // Π fields… (ih…), motive (c_i p… fields…)
            let minor_body = self.abstr_pi_telescope(&ih_locals, motive_app);
            let minor_ty = self.abstr_pi_telescope(&fields, minor_body);
            // Pop the IH locals and the field locals (only needed for minor_ty).
            for _ in 0..ih_locals.len() {
                ctx.pop();
            }
            for _ in 0..fields.len() {
                ctx.pop();
            }
            let minor_fvar = ctx.fresh_fvar();
            let minor_name = self.minor_name(c.name);
            let minor_decl = LocalDecl {
                fvar: minor_fvar,
                name: minor_name,
                ty: minor_ty,
                info: BinderInfo::Default,
            };
            ctx.push(minor_decl);
            minors.push(minor_decl);
            ctor_fields.push(fields);
        }

        // major : I p_1…p_m
        let major_fvar = ctx.fresh_fvar();
        let major_name = self.name_str_anon("t");
        let major_decl = LocalDecl {
            fvar: major_fvar,
            name: major_name,
            ty: ind_applied,
            info: BinderInfo::Default,
        };
        let major = self.fvar(major_fvar);

        // The result type `motive major`, abstracted over major, minors, motive,
        // params (params outermost — the Lean convention: params before motive).
        let motive_major = self.app(motive, major);
        let rec_ty = self.abstr_pi_telescope(&[major_decl], motive_major);
        let rec_ty = self.abstr_pi_telescope(&minors, rec_ty);
        let rec_ty = self.abstr_pi_telescope(&[motive_decl], rec_ty);
        let rec_ty = self.abstr_pi_telescope(&params, rec_ty);

        // Build the rec rules:
        //   value_i = λ params motive m_1..m_n fields_i…,
        //             m_i fields_i… (I.rec params motive m… f_j)…
        let mut rec_rules: Vec<RecRule> = Vec::with_capacity(ctors.len());
        // The recursor's universe parameters, as `Param` levels, for the inner
        // `I.rec …` calls in recursive ι-rules (instantiated to the const's
        // actual levels by `reduce_rec`).
        let rec_level_args: Vec<crate::level::LevelId> =
            rec_uparams.iter().map(|&u| self.level_param(u)).collect();
        for (i, c) in ctors.iter().enumerate() {
            let minor = minors[i];
            let fields = &ctor_fields[i];
            // m_i fields_i…
            let mut body = self.fvar(minor.fvar);
            for f in fields {
                let fv = self.fvar(f.fvar);
                body = self.app(body, fv);
            }
            // … then one recursive call `I.rec params motive minors… f_j` per
            // recursive field `f_j`, in field order (the IH arguments).
            for &rf in &c.recursive_fields {
                let f = fields[rf];
                let mut rec_call = self.const_(rec_name, rec_level_args.clone());
                for p in &params {
                    let pv = self.fvar(p.fvar);
                    rec_call = self.app(rec_call, pv);
                }
                rec_call = self.app(rec_call, motive);
                for m in &minors {
                    let mv = self.fvar(m.fvar);
                    rec_call = self.app(rec_call, mv);
                }
                let fv = self.fvar(f.fvar);
                rec_call = self.app(rec_call, fv);
                body = self.app(body, rec_call);
            }
            // λ fields_i…, (m_i fields_i… ih…)
            let val = self.abstr_lambda_telescope(fields, body);
            // λ motive m_1..m_n, (…)
            let val = self.abstr_lambda_telescope(&minors, val);
            let val = self.abstr_lambda_telescope(&[motive_decl], val);
            // λ params, (…)   — params outermost (consumed first by ι).
            let val = self.abstr_lambda_telescope(&params, val);
            rec_rules.push(RecRule {
                ctor_name: c.name,
                num_fields: u16::try_from(fields.len()).expect("field count fits u16"),
                value: val,
            });
        }

        // Soundness self-check: the generated recursor type must infer to a
        // `Sort` under the recursor's universe parameters (as `Param`s, which
        // they already are). A failure means the de Bruijn bookkeeping is wrong.
        let mut check_ctx = LocalContext::new();
        let rec_ty_ty = self.infer_core(rec_ty, &mut check_ctx)?;
        let rec_ty_ty = self.whnf(rec_ty_ty);
        if !matches!(self.expr_node(rec_ty_ty), ExprNode::Sort(_)) {
            return Err(KernelError::DeclarationTypeNotASort { got: rec_ty_ty });
        }

        Ok(Declaration::Recursor {
            name: rec_name,
            uparams: rec_uparams,
            ty: rec_ty,
            rec_rules,
            num_motives: 1,
            num_minors: u16::try_from(ctors.len()).expect("ctor count fits u16"),
            num_params: u16::try_from(num_params).expect("param count fits u16"),
            num_indices: 0,
        })
    }

    /// Open the recursor's `num_params` parameter locals into `ctx` (pushing
    /// each), with their types read from the inductive's declared type telescope
    /// `ind_ty`. Returns them outer-to-inner. Each parameter type is
    /// instantiated with the preceding parameter fvars so later parameter types
    /// see earlier parameters.
    fn open_rec_params(
        &mut self,
        ctx: &mut LocalContext,
        num_params: usize,
        ind_ty: ExprId,
    ) -> Vec<LocalDecl> {
        let mut params = Vec::with_capacity(num_params);
        let mut cursor = self.whnf(ind_ty);
        for _ in 0..num_params {
            let ExprNode::Pi(bname, dom, body, info) = self.expr_node(cursor).clone() else {
                break;
            };
            let fvar = ctx.fresh_fvar();
            let decl = LocalDecl {
                fvar,
                name: bname,
                ty: dom,
                info,
            };
            ctx.push(decl);
            params.push(decl);
            let fv = self.fvar(fvar);
            cursor = self.instantiate(body, &[fv]);
            cursor = self.whnf(cursor);
        }
        params
    }

    /// `Const(c, [Param(u)…])` for a constructor sharing the inductive's
    /// universe parameters.
    fn mk_ind_const_for_ctor(&mut self, ctor_name: NameId, uparams: &[NameId]) -> ExprId {
        let levels = uparams.iter().map(|&u| self.level_param(u)).collect();
        self.const_(ctor_name, levels)
    }

    /// Open a constructor's **field** telescope into fresh locals in `ctx`
    /// (pushing each), returning them outer-to-inner. The constructor's leading
    /// `num_params` parameter binders are first skipped, instantiating them with
    /// the recursor's parameter fvars (`params`) so that field types reference
    /// the shared parameters; later field types are instantiated as we go so they
    /// see earlier fields as their fvars.
    fn open_ctor_fields(
        &mut self,
        ctx: &mut LocalContext,
        num_params: usize,
        params: &[LocalDecl],
        c: &CheckedCtor,
    ) -> Vec<LocalDecl> {
        let mut cursor = self.whnf(c.ty);
        // Skip the leading parameter binders, instantiating each with the
        // corresponding shared recursor parameter fvar.
        for p in params.iter().take(num_params) {
            let ExprNode::Pi(_, _, body, _) = self.expr_node(cursor).clone() else {
                break;
            };
            let pv = self.fvar(p.fvar);
            cursor = self.instantiate(body, &[pv]);
            cursor = self.whnf(cursor);
        }
        let mut fields = Vec::with_capacity(c.fields.len());
        while let ExprNode::Pi(bname, dom, body, info) = self.expr_node(cursor).clone() {
            let fvar = ctx.fresh_fvar();
            let decl = LocalDecl {
                fvar,
                name: bname,
                ty: dom,
                info,
            };
            ctx.push(decl);
            fields.push(decl);
            let fv = self.fvar(fvar);
            cursor = self.instantiate(body, &[fv]);
            cursor = self.whnf(cursor);
        }
        fields
    }

    /// Open one induction-hypothesis local `ih_j : motive f_j` in `ctx` (pushing
    /// each) for every recursive field position in `recursive_fields`, in order.
    /// `fields` are the already-opened constructor field locals; `motive` is the
    /// motive fvar expression. Returns the IH locals outer-to-inner.
    fn open_ih_locals(
        &mut self,
        ctx: &mut LocalContext,
        motive: ExprId,
        fields: &[LocalDecl],
        recursive_fields: &[usize],
    ) -> Vec<LocalDecl> {
        let mut ihs = Vec::with_capacity(recursive_fields.len());
        for &rf in recursive_fields {
            let f = fields[rf];
            let fv = self.fvar(f.fvar);
            // ih_j : motive f_j
            let ih_ty = self.app(motive, fv);
            let fvar = ctx.fresh_fvar();
            let name = self.name_str_anon("ih");
            let decl = LocalDecl {
                fvar,
                name,
                ty: ih_ty,
                info: BinderInfo::Default,
            };
            ctx.push(decl);
            ihs.push(decl);
        }
        ihs
    }

    /// A fresh universe parameter name for the recursor's motive level, not
    /// clashing with the inductive's existing universe parameters. Uses `u`,
    /// then `u_1`, `u_2`, … under the anonymous root.
    fn fresh_elim_param(&mut self, uparams: &[NameId]) -> NameId {
        let cand = self.name_str_anon("u");
        if !uparams.contains(&cand) {
            return cand;
        }
        let base = self.anon();
        let u = self.name_str(base, "u");
        let mut i = 1u64;
        loop {
            let cand = self.name_num(u, i);
            if !uparams.contains(&cand) {
                return cand;
            }
            i += 1;
        }
    }

    /// A name `s` appended to the anonymous root.
    fn name_str_anon(&mut self, s: &str) -> NameId {
        let anon = self.anon();
        self.name_str(anon, s)
    }

    /// The minor-premise binder name: the constructor's last string component if
    /// available, else a generic `m`. Cosmetic only (binder names do not affect
    /// checking).
    fn minor_name(&mut self, ctor_name: NameId) -> NameId {
        match self.name_node(ctor_name).clone() {
            crate::name::NameNode::Str(_, s) => self.name_str_anon(&s),
            _ => self.name_str_anon("m"),
        }
    }
}

// ---------------------------------------------------------------------------
// ι-reduction (recursor computation) in WHNF
// ---------------------------------------------------------------------------

impl Kernel {
    /// Try one ι-reduction step on `e` if its head is a recursor `Const(I.rec,
    /// levels)` applied to enough arguments and the major premise WHNFs to a
    /// constructor application of one of `I`'s constructors. Ported from
    /// nanoda's `reduce_rec`, specialized to the parametric, non-indexed scope
    /// (parameters are consumed by both the recursor application and the
    /// constructor application, and threaded into recursive calls by the rule
    /// value).
    ///
    /// Returns `None` for non-recursor heads, too-few arguments, or a major that
    /// is not yet a constructor application (in which case the application is
    /// already weak-head-normal here).
    pub(crate) fn reduce_rec(&mut self, e: ExprId) -> Option<ExprId> {
        let (head, args) = self.unfold_apps(e);
        let ExprNode::Const(rec_name, levels) = self.expr_node(head).clone() else {
            return None;
        };
        let rec = self.env.get_recursor(rec_name)?;
        let major_idx = rec.major_idx();
        let Declaration::Recursor {
            uparams,
            rec_rules,
            num_motives,
            num_minors,
            num_params,
            ..
        } = rec
        else {
            return None;
        };
        // Clone the small bits we need out of the borrow.
        let uparams = uparams.clone();
        let rec_rules = rec_rules.clone();
        // The recursor's leading args are: params + motives + minors, applied to
        // the rule value's λ-telescope (which binds `params motive minors fields…`)
        // before the constructor's fields.
        let prefix_len = (*num_params as usize) + (*num_motives as usize) + (*num_minors as usize);

        let major = *args.get(major_idx)?;
        let major = self.whnf(major);
        let (major_ctor, major_ctor_args) = self.unfold_apps(major);
        let ExprNode::Const(major_ctor_name, _) = self.expr_node(major_ctor).clone() else {
            return None;
        };
        let rule = rec_rules.iter().find(|r| r.ctor_name == major_ctor_name)?;

        // The constructor application is `c params… fields…`: strip the leading
        // parameters (the same count as the recursor's params), keeping only the
        // constructor's fields. `rule.num_fields` is the field count (params
        // excluded). Take the *last* `num_fields` of the ctor args as fields.
        let num_fields = rule.num_fields as usize;
        let extra = major_ctor_args.len().checked_sub(num_fields)?;
        let fields: Vec<ExprId> = major_ctor_args.into_iter().skip(extra).collect();

        // r = rule.value with the recursor's universe parameters instantiated to
        // the const's level arguments.
        if uparams.len() != levels.len() {
            return None;
        }
        let subst = Self::level_subst_for(&uparams, &levels);
        let r = self.substitute_expr_levels(rule.value, &subst);
        // Apply the prefix args (params + motive + minors), then the ctor's
        // fields, then any trailing args after the major. The rule value's
        // λ-telescope binds `params motive minors fields…`, so the prefix args
        // (which include the params) line up positionally.
        let r = self.foldl_apps(r, args.iter().take(prefix_len).copied());
        let r = self.foldl_apps(r, fields);
        let trailing: Vec<ExprId> = args.iter().skip(major_idx + 1).copied().collect();
        Some(self.foldl_apps(r, trailing))
    }

    /// Positional `Param ↦ level` substitution (a small public shim around the
    /// private builder in `tc.rs`).
    fn level_subst_for(
        uparams: &[NameId],
        levels: &[crate::level::LevelId],
    ) -> Vec<(NameId, crate::level::LevelId)> {
        uparams
            .iter()
            .copied()
            .zip(levels.iter().copied())
            .collect()
    }
}

#[cfg(test)]
mod inductive_tests;
