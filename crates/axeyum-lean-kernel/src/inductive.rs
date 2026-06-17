//! The inductive layer (ADR-0036, slice 5): the trusted [`Kernel::add_inductive`]
//! admission gate, recursor generation (with induction hypotheses), and
//! ι-reduction in WHNF.
//!
//! ## Scope — direct-recursive inductives (still non-parametric, non-indexed)
//!
//! This slice supports inductive types that are **non-parametric, non-indexed**,
//! whose constructors may have **direct recursive fields**: an inductive
//! `I : Sort u` whose constructors are `c : T_1 → … → T_k → I` where each field
//! type `T_i` is either non-recursive (does not mention `I`) **or** is exactly
//! the bare recursive occurrence `Const(I, uparams)` (a direct recursive field,
//! e.g. `Nat.succ : Nat → Nat`, or a binary tree's two `Tree` fields). This adds
//! recursive types (`Nat`, binary trees) to the enums and simple structures of
//! slice 4.
//!
//! Direct recursive fields are trivially strictly-positive, so no positivity
//! analysis is required here. Each recursive field is, however, verified to be
//! *exactly* `Const(I, uparams)`: any other occurrence of `I` is rejected.
//!
//! **Deferred** (and rejected explicitly, never guessed): **higher-order /
//! reflexive** recursive fields (`(A → I)` — a field whose type is a `Pi`
//! ending in `I`; only a *bare* `I` field is allowed this slice, reported as
//! [`KernelError::ReflexiveOrNestedNotSupported`]), parameters (`List α`),
//! indices (`Vector`/`Eq`), nested and mutual inductives, and the
//! `Prop`-subsingleton large-elimination subtleties. The motive is always
//! allowed to eliminate into an arbitrary `Sort v` here (the "basic" rule,
//! matching nanoda's large-elimination path for non-`Prop` types); for a
//! `Prop`-valued inductive this is more permissive than Lean's restriction and
//! is a known limitation of this slice.
//!
//! ## What is built
//!
//! For a checked inductive `I` with constructors `c_1 … c_n`, where constructor
//! `c_i` has fields `f_1 … f_k` of which `f_{j1} … f_{jr}` are recursive:
//!
//! - `I.rec : Π {motive : I → Sort v}
//!            (m_1 : Π fields_1 (ih…), motive (c_1 fields_1)) …
//!            (m_n : Π fields_n (ih…), motive (c_n fields_n))
//!            (major : I), motive major`
//!   where each minor premise `m_i` adds, after its `k` field binders, **one
//!   induction-hypothesis binder `ih_j : motive f_j` per recursive field `f_j`**
//!   (in field order; a non-recursive constructor adds none, matching slice 4).
//! - one [`RecRule`] per constructor, with
//!   `value = λ motive m_1 … m_n (fields_i…), m_i fields_i… (I.rec motive m… f_j)…`
//!   — the ι-RHS applies the minor to the fields and then to one recursive call
//!   `I.rec motive minors… f_j` per recursive field `f_j`.
//!
//! The generated recursor's type is itself `infer`-checked (a self-check):
//! a wrong recursor (e.g. a mis-indexed induction hypothesis) would wrongly
//! accept proofs, so it is verified rather than trusted.

use crate::env::{Declaration, RecRule};
use crate::expr::{ExprId, ExprNode};
use crate::name::NameId;
use crate::tc::{KernelError, LocalContext, LocalDecl};
use crate::{BinderInfo, Kernel};

impl Kernel {
    /// Type-check and admit an inductive type together with its constructors —
    /// the **trusted inductive gate** (ADR-0036, slice 5).
    ///
    /// `ty` is the inductive's type (a `Sort` in this slice — no parameters or
    /// indices). `ctors` pairs each constructor's name with its type, in
    /// declaration order. On success this registers the [`Declaration::Inductive`],
    /// one [`Declaration::Constructor`] per constructor, and the generated
    /// [`Declaration::Recursor`] (whose type is `infer`-checked).
    ///
    /// Admission requires:
    ///
    /// 1. no declaration with the inductive's (or any constructor's) name exists;
    /// 2. `ty` is a `Sort` (a non-parametric, non-indexed inductive);
    /// 3. each constructor's type is a telescope `Π (fields…), I` whose field
    ///    types type-check and whose result head is exactly `Const(I, uparams)`.
    ///    A field type may be non-recursive (it does not mention `I`) or a
    ///    **direct recursive field** (its type is exactly `Const(I, uparams)`).
    ///    Any other occurrence of `I` in a field — a reflexive/higher-order
    ///    field (`(A → I)`) or a parametric/indexed self-reference (`I a`) — is
    ///    rejected.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError::DeclarationExists`] for a duplicate name,
    /// [`KernelError::InductiveTypeNotASort`] if `ty` is not a `Sort`,
    /// [`KernelError::ReflexiveOrNestedNotSupported`] for a reflexive/nested
    /// recursive field, [`KernelError::RecursiveInductiveNotSupported`] for a
    /// parametric/indexed self-reference, [`KernelError::ConstructorResultMismatch`] /
    /// [`KernelError::MalformedConstructorType`] for a wrong/ill-formed
    /// constructor result, or any [`KernelError`] surfaced while inferring a
    /// field type or the generated recursor type.
    ///
    /// # Panics
    ///
    /// Does not panic on well-formed or ill-formed input; all rejections are
    /// returned as [`KernelError`]s.
    pub fn add_inductive(
        &mut self,
        name: NameId,
        uparams: &[NameId],
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

        // (2) The inductive's type must be a `Sort` (non-parametric/non-indexed).
        // It must first itself type-check (its type infers to a Sort-of-a-Sort).
        let mut ctx = LocalContext::new();
        let ty_ty = self.infer_core(ty, &mut ctx)?;
        let ty_ty = self.whnf(ty_ty);
        if !matches!(self.expr_node(ty_ty), ExprNode::Sort(_)) {
            return Err(KernelError::InductiveTypeNotASort { got: ty_ty });
        }
        let ty_whnf = self.whnf(ty);
        if !matches!(self.expr_node(ty_whnf), ExprNode::Sort(_)) {
            // A `Pi`-headed type would be a parametric/indexed inductive
            // (deferred); any other head is ill-typed for an inductive.
            return Err(KernelError::InductiveTypeNotASort { got: ty_whnf });
        }

        // The inductive constant `Const(I, uparams-as-levels)`, used as the
        // expected result head and for the major premise's type.
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

        let mut checked: Vec<CheckedCtor> = Vec::with_capacity(ctors.len());
        for (idx, (cn, cty)) in ctors.iter().copied().enumerate() {
            match self.check_ctor(name, ind_const, cn, cty) {
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

        // Register the constructors.
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
        match self.mk_recursor(rec_name, uparams, ind_const, &checked) {
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

    /// Check one constructor: open its field telescope into fresh locals,
    /// classifying each field as non-recursive or a **direct recursive field**
    /// (its type is exactly `Const(I, uparams)`), and require the result head to
    /// be exactly the parent inductive `Const(I, uparams)`. Returns the opened
    /// field locals (each carries the binder name/type/info), outer-to-inner,
    /// together with the field positions that are recursive (ascending).
    ///
    /// Any occurrence of `I` in a field type that is *not* a bare direct field
    /// is rejected: a `Pi` ending in `I` (reflexive/higher-order) ⇒
    /// [`KernelError::ReflexiveOrNestedNotSupported`]; a self-reference applied
    /// to arguments (`I a`, parametric/indexed) ⇒
    /// [`KernelError::RecursiveInductiveNotSupported`]; any deeper occurrence ⇒
    /// [`KernelError::ReflexiveOrNestedNotSupported`].
    fn check_ctor(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
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

        let mut fields: Vec<LocalDecl> = Vec::new();
        let mut recursive_fields: Vec<usize> = Vec::new();
        let mut cursor = self.whnf(ctor_ty);
        while let ExprNode::Pi(bname, dom, body, info) = self.expr_node(cursor).clone() {
            // Classify the field's occurrence of `I`, if any. A direct recursive
            // field (`dom == Const(I, uparams)`) is admitted and recorded;
            // everything else mentioning `I` is rejected with a precise error.
            if self.mentions_const(dom, ind_name) {
                if dom == ind_const {
                    // Direct recursive field: exactly `Const(I, uparams)`.
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

        // The telescope must end exactly in the parent inductive constant. In
        // this non-parametric/non-indexed slice that is `Const(I, uparams)`
        // with no applied arguments.
        if cursor != ind_const {
            // Distinguish "wrong head inductive" from "applied (params/indices)".
            let (head, _args) = self.unfold_apps(cursor);
            if let ExprNode::Const(n, _) = self.expr_node(head) {
                if *n == ind_name {
                    // Right inductive, but applied to args ⇒ parametric/indexed.
                    return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
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

    /// Classify a field type `dom` that mentions `I` but is **not** the bare
    /// direct field `Const(I, uparams)`, into the appropriate deferred-error.
    ///
    /// - a `Pi` whose telescope ends in `I` (a reflexive/higher-order field,
    ///   e.g. `(A → I)`) ⇒ [`KernelError::ReflexiveOrNestedNotSupported`];
    /// - a self-reference applied to arguments (`I a…`, parametric/indexed)
    ///   ⇒ [`KernelError::RecursiveInductiveNotSupported`];
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
        // `I` applied to arguments (`Const(I, _) a…`) is a parametric/indexed
        // self-reference: the deferred recursive-with-params machinery.
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
    /// The opened field locals (outer-to-inner), each carrying name/type/info.
    fields: Vec<LocalDecl>,
    /// The 0-based field positions that are **direct recursive fields** (a field
    /// whose type is exactly `Const(I, uparams)`), ascending. One induction
    /// hypothesis (in the recursor's minor premise) and one recursive call (in
    /// the ι-rule) is generated per entry, in this order.
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
    /// inductive. The recursor's type is `infer`-checked before it is returned
    /// (the soundness self-check).
    #[allow(clippy::too_many_lines)]
    fn mk_recursor(
        &mut self,
        rec_name: NameId,
        uparams: &[NameId],
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

        // We work in one shared local context: motive, then the minors. The
        // fields for each constructor live in nested contexts during minor and
        // rec-rule construction.
        let mut ctx = LocalContext::new();

        // motive : I → Sort v   (implicit). No indices ⇒ a plain arrow.
        let motive_ty = {
            // Π (_ : I), Sort v   — the bound var is unused, so the body is a
            // closed `Sort v` (no BVar).
            let anon = self.anon();
            self.pi(anon, ind_const, elim_sort, BinderInfo::Default)
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
            let fields = self.open_ctor_fields(&mut ctx, c);
            // c_i fields…  :  I
            let ctor_app = {
                let head = self.mk_ind_const_for_ctor(c.name, uparams);
                let mut app = head;
                for f in &fields {
                    let fv = self.fvar(f.fvar);
                    app = self.app(app, fv);
                }
                app
            };
            // motive (c_i fields…)
            let motive_app = self.app(motive, ctor_app);
            // One induction-hypothesis binder `ih_j : motive f_j` per recursive
            // field `f_j`, in field order, opened *after* the field binders so
            // each IH's type references the already-bound field fvar. These IH
            // locals are abstracted along with the fields into the minor type, so
            // their de Bruijn indices fall out of `abstr_pi_telescope`.
            let ih_locals = self.open_ih_locals(&mut ctx, motive, &fields, &c.recursive_fields);
            // Π fields… (ih…), motive (c_i fields…)
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

        // major : I
        let major_fvar = ctx.fresh_fvar();
        let major_name = self.name_str_anon("t");
        let major_decl = LocalDecl {
            fvar: major_fvar,
            name: major_name,
            ty: ind_const,
            info: BinderInfo::Default,
        };
        let major = self.fvar(major_fvar);

        // The result type `motive major`, abstracted over major, minors, motive.
        let motive_major = self.app(motive, major);
        let rec_ty = self.abstr_pi_telescope(&[major_decl], motive_major);
        let rec_ty = self.abstr_pi_telescope(&minors, rec_ty);
        let rec_ty = self.abstr_pi_telescope(&[motive_decl], rec_ty);

        // Build the rec rules: value_i = λ motive m_1..m_n fields_i…, m_i fields_i…
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
            // … then one recursive call `I.rec motive minors… f_j` per recursive
            // field `f_j`, in field order (the induction-hypothesis arguments).
            for &rf in &c.recursive_fields {
                let f = fields[rf];
                let mut rec_call = self.const_(rec_name, rec_level_args.clone());
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
            num_params: 0,
            num_indices: 0,
        })
    }

    /// `Const(c, [Param(u)…])` for a constructor sharing the inductive's
    /// universe parameters.
    fn mk_ind_const_for_ctor(&mut self, ctor_name: NameId, uparams: &[NameId]) -> ExprId {
        let levels = uparams.iter().map(|&u| self.level_param(u)).collect();
        self.const_(ctor_name, levels)
    }

    /// Open a constructor's field telescope into fresh locals in `ctx` (pushing
    /// each), returning them outer-to-inner. The field types are instantiated as
    /// we go so later field types see earlier fields as their fvars.
    fn open_ctor_fields(&mut self, ctx: &mut LocalContext, c: &CheckedCtor) -> Vec<LocalDecl> {
        let mut fields = Vec::with_capacity(c.fields.len());
        let mut cursor = self.whnf(c.ty);
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
    /// nanoda's `reduce_rec`, specialized to the non-parametric, non-indexed,
    /// non-recursive scope (no params/indices/recursive args to handle).
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
        let prefix_len = (*num_params + *num_motives + *num_minors) as usize;

        let major = *args.get(major_idx)?;
        let major = self.whnf(major);
        let (major_ctor, major_ctor_args) = self.unfold_apps(major);
        let ExprNode::Const(major_ctor_name, _) = self.expr_node(major_ctor).clone() else {
            return None;
        };
        let rule = rec_rules.iter().find(|r| r.ctor_name == major_ctor_name)?;

        // No params/indices in this slice, so all ctor args are fields.
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
        // Apply the prefix args (motive + minors), then the ctor's fields, then
        // any trailing args after the major.
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
