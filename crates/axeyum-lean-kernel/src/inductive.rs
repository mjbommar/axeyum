//! The inductive layer (ADR-0036, slice 7): the trusted [`Kernel::add_inductive`]
//! admission gate, recursor generation (with induction hypotheses, parameters,
//! and **indices**), and ι-reduction in WHNF.
//!
//! ## Scope — parametric, direct-recursive, and (non-recursive) indexed
//!
//! This slice supports inductive types that are **parametric** (`m` leading
//! parameter binders fixed across the family) and **indexed** (`k` further
//! binders — the *indices* — before the final `Sort`). An inductive
//! `I : Π (p_1 … p_m) (idx_1 … idx_k), Sort u` opens the `m` parameters then the
//! `k` indices; the remainder must be exactly a `Sort`. The backbone target is
//! `Eq.{u} {α : Sort u} (a : α) : α → Prop` (2 params, 1 index).
//!
//! Each constructor is `c : Π (p_1…p_m) (fields…), I p_1…p_m e_1…e_k`: it
//! re-binds the **same** `m` parameters (whose types must be def-eq to the
//! inductive's), then its fields, and its result is the inductive applied to
//! those `m` parameter binders **and** `k` **index argument expressions**
//! `e_1…e_k` that may depend on the params and fields. The recursor's motive
//! ranges over the indices and the major
//! (`motive : Π (indices), (I p… indices) → Sort v`); each minor applies the
//! motive to the **constructor's own** index expressions. This unlocks `Eq`
//! (and simple indexed enums), on top of the slice-6 parametric families
//! (`List`, `Option`, `Prod`, `Sum`), the slice-5 recursive types (`Nat`,
//! trees), and the slice-4 enums/structures.
//!
//! Every non-parameter constructor field first passes Lean 4.30's strict-
//! positivity rule (ADR-0352/TL2.11): after WHNF, no occurrence is accepted; a
//! `Pi` is accepted only when its domain contains no `I` and its codomain is
//! recursively positive; every other occurrence must be the exact `I p… idx…`
//! application with fixed parameters, complete index arity, and occurrence-free
//! indices. This preflight runs before provisional environment insertion.
//!
//! A field is a **direct recursive field** iff its type is exactly `I p_1…p_m`
//! (only for a **non-indexed** family, `k = 0`). The positivity guard is broader
//! than the currently admitted recursive profile: positive recursive-indexed
//! and reflexive fields pass it, then retain their explicit feature declines.
//!
//! **Deferred** (and rejected explicitly, never guessed): **recursive
//! constructors on an indexed inductive** (recursion + indices together, e.g.
//! `Vector.cons` — a field mentioning `I` when `num_indices > 0`, reported as
//! [`KernelError::RecursiveIndexedNotSupported`]), **higher-order / reflexive**
//! recursive fields (`(A → I p…)` — a field whose type is a `Pi` ending in `I`,
//! reported as [`KernelError::ReflexiveOrNestedNotSupported`]), nested and
//! mutual inductives.
//!
//! `Prop` elimination follows Lean's syntactic-subsingleton rule. An inductive
//! whose result universe is provably nonzero may eliminate into an arbitrary
//! `Sort v`. A family that may inhabit `Prop` may do so only when it is empty,
//! or has exactly one constructor and every non-`Prop` field occurs as an exact
//! argument of that constructor's result. Every other such family receives a
//! recursor whose motive is restricted to `Prop` (`Sort 0`). This restriction
//! is required for soundness in the presence of proof irrelevance.
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
    /// the **trusted inductive gate** (ADR-0036, slice 7).
    ///
    /// `num_params` is the number of leading binders of `ty` that are
    /// **parameters** (fixed across the family); the caller declares this,
    /// mirroring Lean's export. After opening those `m = num_params` parameter
    /// binders, any further binders of `ty` are **indices** (opened as fresh
    /// index fvars), and the remainder must WHNF to a `Sort`. `ctors` pairs each
    /// constructor's name with its type, in declaration order. On success this
    /// registers the [`Declaration::Inductive`], one [`Declaration::Constructor`]
    /// per constructor, and the generated [`Declaration::Recursor`] (whose type
    /// is `infer`-checked).
    ///
    /// Admission requires:
    ///
    /// 1. no declaration with the inductive's (or any constructor's) name exists;
    /// 2. `ty` opens `num_params` parameter binders then `num_indices` index
    ///    binders and then WHNFs to a `Sort`;
    /// 3. every non-parameter constructor field passes Lean 4.30 strict
    ///    positivity before any provisional environment insertion;
    /// 4. each constructor's type re-binds the **same** `num_params` parameters
    ///    (their types def-eq to the inductive's), then a telescope of fields
    ///    whose types type-check and whose result head is the inductive applied
    ///    to those parameters in order followed by `num_indices` index argument
    ///    expressions. A field type may be non-recursive (it does not mention
    ///    `I`) or — only for a **non-indexed** family — a **direct recursive
    ///    field** (its type is exactly `I p_1…p_m`). A field mentioning `I` on an
    ///    indexed family, or any other non-direct occurrence of `I`, is rejected.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError::DeclarationExists`] for a duplicate name,
    /// [`KernelError::InductiveTypeNotASort`] if `ty`'s param+index-stripped tail
    /// is not a `Sort`, [`KernelError::RecursiveIndexedNotSupported`] for a
    /// recursive field on an indexed family (deferred),
    /// [`KernelError::NonPositiveInductiveOccurrence`] for a family occurrence
    /// in a function domain, [`KernelError::InvalidInductiveOccurrence`] for a
    /// containing term that is not a valid family application,
    /// [`KernelError::ReflexiveOrNestedNotSupported`] for a positive but
    /// unsupported reflexive/nested
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
    #[allow(clippy::too_many_lines)]
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
        // The binders remaining after the parameters are the **indices**
        // (ADR-0036, slice 7): open them as fresh index fvars (their telescope
        // types may reference the parameters and earlier indices). After the
        // indices the tail must be exactly a `Sort`.
        let mut indices: Vec<LocalDecl> = Vec::new();
        while let ExprNode::Pi(bname, dom, body, info) = self.expr_node(cursor).clone() {
            let fvar = ctx.fresh_fvar();
            let decl = LocalDecl {
                fvar,
                name: bname,
                ty: dom,
                info,
            };
            ctx.push(decl);
            indices.push(decl);
            let fv = self.fvar(fvar);
            cursor = self.instantiate(body, &[fv]);
            cursor = self.whnf(cursor);
        }
        let num_indices = indices.len();
        // The remainder must be exactly a `Sort` after params + indices.
        let ExprNode::Sort(result_level) = self.expr_node(cursor) else {
            return Err(KernelError::InductiveTypeNotASort { got: cursor });
        };
        let result_level = *result_level;

        // The inductive constant `Const(I, uparams-as-levels)`, used as the
        // applied result head and for the major premise's type.
        let ind_const = self.mk_ind_const(name, uparams);

        // TL2.11 / ADR-0352: positivity is a distinct trusted preflight, not an
        // accidental consequence of the later feature-decline paths. Run it
        // before the temporary `Inductive` declaration is inserted below.
        for &(ctor_name, ctor_ty) in ctors {
            self.check_constructor_positivity(
                name,
                ind_const,
                num_params,
                num_indices,
                &params,
                ctor_name,
                ctor_ty,
            )?;
        }

        // (4) Check each constructor and collect its opened field locals.
        //
        // We register the Inductive declaration FIRST (so field types and the
        // recursor type, which reference `Const(I, …)`, resolve), then validate
        // every constructor; if a constructor fails we roll the inductive back.
        let ctor_names: Vec<NameId> = ctors.iter().map(|(n, _)| *n).collect();
        self.env.insert_unchecked(Declaration::Inductive {
            name,
            uparams: uparams.to_vec(),
            ty,
            num_params: u16::try_from(num_params).expect("parameter count fits u16"),
            num_indices: u16::try_from(num_indices).expect("index count fits u16"),
            is_recursive: false,
            ctor_names: ctor_names.clone(),
        });

        // The inductive's shared parameter locals, threaded into each
        // constructor check so dependent parameter types and field/result
        // references resolve to the same fvars as the inductive.
        let shared_params = params.clone();

        let mut checked: Vec<CheckedCtor> = Vec::with_capacity(ctors.len());
        for (idx, (cn, cty)) in ctors.iter().copied().enumerate() {
            match self.check_ctor(
                name,
                ind_const,
                num_params,
                num_indices,
                &shared_params,
                cn,
                cty,
            ) {
                Ok((fields, recursive_fields, exposes_non_prop_fields)) => {
                    checked.push(CheckedCtor {
                        name: cn,
                        ty: cty,
                        idx: u16::try_from(idx).expect("ctor count fits u16"),
                        fields,
                        recursive_fields,
                        exposes_non_prop_fields,
                    });
                }
                Err(e) => {
                    // Roll back the inductive so the environment is unchanged.
                    self.env.remove_unchecked(name);
                    return Err(e);
                }
            }
        }

        // Constructor checking is the trusted point at which direct recursive
        // fields are classified. Persist the aggregate bit on the inductive so
        // structure eta can implement Lean's exact `is_non_rec_structure`
        // predicate without re-scanning raw constructor syntax later.
        let is_recursive = checked
            .iter()
            .any(|constructor| !constructor.recursive_fields.is_empty());
        self.env.insert_unchecked(Declaration::Inductive {
            name,
            uparams: uparams.to_vec(),
            ty,
            num_params: u16::try_from(num_params).expect("parameter count fits u16"),
            num_indices: u16::try_from(num_indices).expect("index count fits u16"),
            is_recursive,
            ctor_names,
        });

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
        let allows_large_elimination = self.level_is_nonzero(result_level)
            || match checked.as_slice() {
                [] => true,
                [ctor] => ctor.exposes_non_prop_fields,
                _ => false,
            };
        match self.mk_recursor(
            rec_name,
            name,
            uparams,
            num_params,
            num_indices,
            ty,
            ind_const,
            &checked,
            allows_large_elimination,
        ) {
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

    /// Check Lean 4.30 strict positivity for every non-parameter field in one
    /// constructor telescope, before the family is inserted into the
    /// environment. Malformed parameter telescopes are left to the existing
    /// typed constructor check so this preflight does not steal unrelated error
    /// classifications.
    #[allow(clippy::too_many_arguments)]
    fn check_constructor_positivity(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
        num_params: usize,
        num_indices: usize,
        params: &[LocalDecl],
        ctor_name: NameId,
        ctor_ty: ExprId,
    ) -> Result<(), KernelError> {
        let mut ctx = LocalContext::new();
        let mut param_values = Vec::with_capacity(num_params);
        for param in params.iter().take(num_params) {
            ctx.bump_fresh_above(param.fvar);
            ctx.push(*param);
            param_values.push(self.fvar(param.fvar));
        }

        let mut cursor = self.whnf(ctor_ty);
        for &param in &param_values {
            let ExprNode::Pi(_, _, body, _) = self.expr_node(cursor).clone() else {
                return Ok(());
            };
            cursor = self.instantiate(body, &[param]);
            cursor = self.whnf(cursor);
        }

        let mut field_index = 0_u32;
        while let ExprNode::Pi(bname, domain, body, info) = self.expr_node(cursor).clone() {
            self.check_positive_occurrence(
                ind_name,
                ind_const,
                num_indices,
                &param_values,
                ctor_name,
                field_index,
                domain,
                &mut ctx,
            )?;

            let fvar = ctx.fresh_fvar();
            let local = LocalDecl {
                fvar,
                name: bname,
                ty: domain,
                info,
            };
            ctx.push(local);
            let value = self.fvar(fvar);
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
            field_index = field_index
                .checked_add(1)
                .ok_or(KernelError::MalformedConstructorType { ctor: ctor_name })?;
        }
        Ok(())
    }

    /// Lean 4.30's `check_positivity` rule for the currently representable
    /// single-family declaration profile.
    #[allow(clippy::too_many_arguments)]
    fn check_positive_occurrence(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
        num_indices: usize,
        param_values: &[ExprId],
        ctor_name: NameId,
        field_index: u32,
        term: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<(), KernelError> {
        let term = self.whnf(term);
        if !self.mentions_const(term, ind_name) {
            return Ok(());
        }

        if let ExprNode::Pi(bname, domain, body, info) = self.expr_node(term).clone() {
            if self.mentions_const(domain, ind_name) {
                return Err(KernelError::NonPositiveInductiveOccurrence {
                    inductive: ind_name,
                    ctor: ctor_name,
                    field_index,
                });
            }
            let fvar = ctx.fresh_fvar();
            let local = LocalDecl {
                fvar,
                name: bname,
                ty: domain,
                info,
            };
            ctx.push(local);
            let value = self.fvar(fvar);
            let body = self.instantiate(body, &[value]);
            let result = self.check_positive_occurrence(
                ind_name,
                ind_const,
                num_indices,
                param_values,
                ctor_name,
                field_index,
                body,
                ctx,
            );
            ctx.pop();
            return result;
        }

        if self.is_valid_positive_inductive_application(
            term,
            ind_name,
            ind_const,
            num_indices,
            param_values,
        ) {
            return Ok(());
        }

        Err(KernelError::InvalidInductiveOccurrence {
            inductive: ind_name,
            ctor: ctor_name,
            field_index,
        })
    }

    /// Whether `term` is exactly `I params indices`, with the declared universe
    /// instantiation and no family occurrence inside an index.
    fn is_valid_positive_inductive_application(
        &self,
        term: ExprId,
        ind_name: NameId,
        ind_const: ExprId,
        num_indices: usize,
        param_values: &[ExprId],
    ) -> bool {
        let (head, args) = self.unfold_apps(term);
        if head != ind_const || args.len() != param_values.len() + num_indices {
            return false;
        }
        if args[..param_values.len()] != param_values[..] {
            return false;
        }
        args[param_values.len()..]
            .iter()
            .all(|&index| !self.mentions_const(index, ind_name))
    }

    /// Check one constructor of a parametric, possibly indexed inductive: open
    /// its leading parameter telescope re-bound to the inductive's **shared**
    /// parameter locals `params` (each binder's declared domain must be def-eq to
    /// the shared parameter's type, so dependent parameters — e.g. `Eq`'s
    /// `a : α` — resolve correctly), then its field telescope into fresh locals,
    /// and require the result head to be `I p_1…p_m e_1…e_k` (the inductive
    /// applied to the shared parameters then `num_indices` index argument
    /// expressions). Returns the opened **field** locals (outer-to-inner; the
    /// parameters are *not* included) together with stable recursive-field
    /// descriptors (ascending by field position; always empty for an indexed
    /// family while recursive-indexed admission is deferred).
    ///
    /// A field is a **direct recursive field** (recorded) only on a non-indexed
    /// family (`num_indices == 0`) and only if its type is exactly `I p_1…p_m`.
    /// On an indexed family any field mentioning `I` ⇒
    /// [`KernelError::RecursiveIndexedNotSupported`]. Otherwise a `Pi` ending in
    /// `I` (reflexive/higher-order) ⇒
    /// [`KernelError::ReflexiveOrNestedNotSupported`]; a self-reference applied
    /// to the wrong arguments ⇒ [`KernelError::RecursiveInductiveNotSupported`].
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn check_ctor(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
        num_params: usize,
        num_indices: usize,
        params: &[LocalDecl],
        ctor_name: NameId,
        ctor_ty: ExprId,
    ) -> Result<(Vec<LocalDecl>, Vec<RecursiveField>, bool), KernelError> {
        // Open the constructor's telescope in a context seeded with the
        // inductive's **shared** parameter locals, so that dependent parameter
        // types (e.g. `Eq`'s `a : α` referencing the earlier param `α`) and the
        // field/result references all resolve to the same parameter fvars as the
        // inductive itself.
        let mut ctx = LocalContext::new();
        for p in params.iter().take(num_params) {
            ctx.push(*p);
            ctx.bump_fresh_above(p.fvar);
        }
        // The constructor's type must itself type-check (to a Sort).
        let cty_ty = self.infer_core(ctor_ty, &mut ctx)?;
        let cty_ty = self.whnf(cty_ty);
        if !matches!(self.expr_node(cty_ty), ExprNode::Sort(_)) {
            return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
        }

        let mut cursor = self.whnf(ctor_ty);

        // Open the `num_params` leading parameter binders, instantiating each
        // with the inductive's **shared** parameter fvar (so the constructor
        // re-binds the SAME parameters). Each binder's declared domain must be
        // def-eq to the inductive's corresponding parameter type.
        let param_locals: Vec<LocalDecl> = params.iter().take(num_params).copied().collect();
        for p in &param_locals {
            let ExprNode::Pi(_bname, dom, body, _info) = self.expr_node(cursor).clone() else {
                // Fewer leading binders than parameters ⇒ the constructor does
                // not re-bind all parameters.
                return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
            };
            if !self.def_eq(dom, p.ty) {
                return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
            }
            let pv = self.fvar(p.fvar);
            cursor = self.instantiate(body, &[pv]);
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
        let param_values: Vec<ExprId> = param_locals
            .iter()
            .map(|param| self.fvar(param.fvar))
            .collect();
        let mut recursive_fields: Vec<RecursiveField> = Vec::new();
        // Lean's large-elimination test records every non-parameter field whose
        // type does not inhabit Prop, then requires each such field itself to
        // occur as an exact argument of the constructor result. This is more
        // precise than merely searching beneath an index expression: the field
        // value must be recoverable directly from the result type.
        let mut non_prop_field_values: Vec<ExprId> = Vec::new();
        while let ExprNode::Pi(bname, dom, body, info) = self.expr_node(cursor).clone() {
            let dom_type = self.infer_core(dom, &mut ctx)?;
            let dom_type = self.whnf(dom_type);
            let ExprNode::Sort(dom_level) = self.expr_node(dom_type) else {
                return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
            };
            let field_is_proof = self.level_is_zero(*dom_level);

            // M1 / ADR-0353: every positive recursive shape is inspected by one
            // WHNF telescope-tail path. This checkpoint records only the stable
            // descriptor for the already-supported zero-telescope/zero-index
            // direct case; indexed and higher-order shapes retain their feature
            // declines until M2.
            let recursive_shape = self.open_recursive_field_shape(
                ind_name,
                ind_const,
                num_indices,
                &param_values,
                dom,
                None,
                &mut ctx,
            );
            if self.mentions_const(dom, ind_name)
                && let Some(recursive_field) = self.classify_recursive_field_under_m1_declines(
                    ind_name,
                    ind_const,
                    num_indices,
                    ctor_name,
                    dom,
                    ind_applied,
                    fields.len(),
                    recursive_shape,
                )?
            {
                recursive_fields.push(recursive_field);
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
            if !field_is_proof {
                non_prop_field_values.push(fv);
            }
            cursor = self.instantiate(body, &[fv]);
            cursor = self.whnf(cursor);
        }

        // The telescope must end exactly in `I p_1…p_m idx_1…idx_k`: the
        // inductive applied to the constructor's parameters (fixed) then
        // `num_indices` **index argument expressions** (which may depend on the
        // params and fields). Split the result's spine into head + args, require
        // the head to be `I`, the leading `num_params` args to be exactly the
        // parameter fvars, and collect the remaining `num_indices` index exprs.
        let (head, args) = self.unfold_apps(cursor);
        let head_ok = matches!(self.expr_node(head), ExprNode::Const(n, _) if *n == ind_name);
        if !head_ok || args.len() != num_params + num_indices {
            return Err(KernelError::ConstructorResultMismatch {
                expected: ind_name,
                ctor: ctor_name,
            });
        }
        for (i, p) in param_locals.iter().enumerate() {
            let pv = self.fvar(p.fvar);
            if args[i] != pv {
                // The result applies `I` to a non-parameter in a parameter
                // position (wrong params).
                return Err(KernelError::ConstructorResultMismatch {
                    expected: ind_name,
                    ctor: ctor_name,
                });
            }
        }
        // The trailing `num_indices` args are the constructor's own index
        // expressions; they are re-derived (freshly, in the recursor's own
        // fvars) during `mk_recursor`, so they need not be returned here.
        let exposes_non_prop_fields = non_prop_field_values
            .iter()
            .all(|field| args.contains(field));
        Ok((fields, recursive_fields, exposes_non_prop_fields))
    }

    /// Apply M1's frozen admission policy to a structurally recursive field
    /// after the shared WHNF helper has inspected it. Only the exact historical
    /// direct surface form receives metadata. Every other surface form keeps
    /// its pre-M1 feature-decline precedence until M2 explicitly widens it.
    #[allow(clippy::too_many_arguments)]
    fn classify_recursive_field_under_m1_declines(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
        num_indices: usize,
        ctor_name: NameId,
        dom: ExprId,
        ind_applied: ExprId,
        field_index: usize,
        recursive_shape: Option<OpenedRecursiveField>,
    ) -> Result<Option<RecursiveField>, KernelError> {
        if dom == ind_applied {
            let Some(shape) = recursive_shape else {
                return Err(KernelError::RecursiveFieldShapeMismatch {
                    inductive: ind_name,
                    ctor: ctor_name,
                    field_index: u32::try_from(field_index).unwrap_or(u32::MAX),
                });
            };
            return Ok(Some(RecursiveField {
                field_index,
                telescope_depth: shape.telescope.len(),
            }));
        }
        if matches!(self.expr_node(dom), ExprNode::Pi(..)) {
            return Err(KernelError::ReflexiveOrNestedNotSupported {
                inductive: ind_name,
                ctor: ctor_name,
            });
        }
        if num_indices != 0 {
            let (head, _) = self.unfold_apps(dom);
            if head == ind_const {
                return Err(KernelError::RecursiveIndexedNotSupported {
                    inductive: ind_name,
                    ctor: ctor_name,
                });
            }
        }
        Err(self.classify_bad_recursive_field(ind_name, ind_const, ctor_name, dom))
    }

    /// Open one field through Lean's shared recursive-argument shape: WHNF at
    /// every step, open a possibly empty `Pi` telescope, then require the exact
    /// family application with fixed parameters and complete occurrence-free
    /// indices. When `recursive_value` is present, apply it to the opened
    /// telescope in lockstep. All temporary locals are popped before return;
    /// callers receive expressions to abstract, never a mutated context.
    #[allow(clippy::too_many_arguments)]
    fn open_recursive_field_shape(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
        num_indices: usize,
        param_values: &[ExprId],
        field_ty: ExprId,
        recursive_value: Option<ExprId>,
        ctx: &mut LocalContext,
    ) -> Option<OpenedRecursiveField> {
        let mut cursor = self.whnf(field_ty);
        let mut telescope = Vec::new();
        let mut applied_value = recursive_value;
        let mut valid_domains = true;
        while let ExprNode::Pi(name, domain, body, info) = self.expr_node(cursor).clone() {
            if self.mentions_const(domain, ind_name) {
                valid_domains = false;
                break;
            }
            let fvar = ctx.fresh_fvar();
            let local = LocalDecl {
                fvar,
                name,
                ty: domain,
                info,
            };
            ctx.push(local);
            telescope.push(local);
            let value = self.fvar(fvar);
            if let Some(applied) = applied_value {
                applied_value = Some(self.app(applied, value));
            }
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
        }

        let (head, args) = self.unfold_apps(cursor);
        let valid_tail = valid_domains
            && head == ind_const
            && args.len() == param_values.len() + num_indices
            && args[..param_values.len()] == param_values[..]
            && args[param_values.len()..]
                .iter()
                .all(|&index| !self.mentions_const(index, ind_name));
        for _ in 0..telescope.len() {
            ctx.pop();
        }
        if valid_tail {
            Some(OpenedRecursiveField {
                telescope,
                indices: args[param_values.len()..].to_vec(),
                applied_value,
            })
        } else {
            None
        }
    }

    /// Reopen a checked recursive field in the recursor's current local
    /// context. Constructor metadata stores only a stable field position and
    /// telescope depth; the dependent telescope, tail indices, and applied
    /// recursive value are rederived by the same helper used for
    /// classification. Any disagreement is a typed internal failure.
    #[allow(clippy::too_many_arguments)]
    fn reopen_recursive_field(
        &mut self,
        ind_name: NameId,
        ind_const: ExprId,
        num_indices: usize,
        param_values: &[ExprId],
        ctor_name: NameId,
        descriptor: RecursiveField,
        fields: &[LocalDecl],
        ctx: &mut LocalContext,
    ) -> Result<OpenedRecursiveField, KernelError> {
        let field_index = u32::try_from(descriptor.field_index).unwrap_or(u32::MAX);
        let Some(field) = fields.get(descriptor.field_index).copied() else {
            return Err(KernelError::RecursiveFieldShapeMismatch {
                inductive: ind_name,
                ctor: ctor_name,
                field_index,
            });
        };
        let field_value = self.fvar(field.fvar);
        let Some(opened) = self.open_recursive_field_shape(
            ind_name,
            ind_const,
            num_indices,
            param_values,
            field.ty,
            Some(field_value),
            ctx,
        ) else {
            return Err(KernelError::RecursiveFieldShapeMismatch {
                inductive: ind_name,
                ctor: ctor_name,
                field_index,
            });
        };
        if opened.telescope.len() != descriptor.telescope_depth || opened.applied_value.is_none() {
            return Err(KernelError::RecursiveFieldShapeMismatch {
                inductive: ind_name,
                ctor: ctor_name,
                field_index,
            });
        }
        Ok(opened)
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
            ExprNode::Proj(_, _, structure) => self.mentions_const(structure, target),
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
    /// Stable descriptors for the recursive fields, ascending by 0-based field
    /// position (within `fields`, parameters excluded). M1 records only the
    /// already-supported empty-telescope/empty-index direct shape; the
    /// telescope depth is retained so M2 can generalize without replacing this
    /// metadata boundary.
    /// One induction hypothesis (in the recursor's minor premise) and one
    /// recursive call (in the ι-rule) is generated per entry, in this order.
    /// Empty for an indexed inductive (recursive-indexed is deferred).
    recursive_fields: Vec<RecursiveField>,
    /// Whether every non-`Prop` field is exposed as an exact argument of this
    /// constructor's result. For a sole constructor of a potentially-`Prop`
    /// family, this is Lean's final syntactic-subsingleton condition for large
    /// elimination.
    exposes_non_prop_fields: bool,
}

/// The context-independent part of a recursive field opened during constructor
/// checking. Fresh telescope locals and tail indices never escape their local
/// context.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RecursiveField {
    field_index: usize,
    telescope_depth: usize,
}

/// A recursive field's validated WHNF telescope-tail shape before it receives a
/// stable constructor-field position.
#[derive(Clone, Debug, PartialEq, Eq)]
struct OpenedRecursiveField {
    telescope: Vec<LocalDecl>,
    indices: Vec<ExprId>,
    applied_value: Option<ExprId>,
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
    /// parametric, possibly **indexed** inductive. The recursor's type is
    /// `infer`-checked before it is returned (the soundness self-check).
    ///
    /// The recursor binds, outer-to-inner: the parameters `p_1…p_m`, the implicit
    /// motive `{motive : Π (indices), (I p… indices) → Sort v}`, the minor
    /// premises, the indices `(indices)`, and the major
    /// `(major : I p… indices)`, yielding `motive indices major`. The parameters
    /// are threaded into every constructor application and recursive `motive`
    /// application; the motive in each minor is applied to the **constructor's
    /// own index expressions** (the crux of the indexed eliminator).
    #[allow(clippy::too_many_lines, clippy::too_many_arguments)]
    fn mk_recursor(
        &mut self,
        rec_name: NameId,
        ind_name: NameId,
        uparams: &[NameId],
        num_params: usize,
        num_indices: usize,
        ind_ty: ExprId,
        ind_const: ExprId,
        ctors: &[CheckedCtor],
        allows_large_elimination: bool,
    ) -> Result<Declaration, KernelError> {
        // Large-eliminating recursors receive a fresh universe parameter `v`,
        // distinct from the inductive's uparams, and expose `[v] ++ uparams`.
        // A non-subsingleton family that may inhabit Prop instead fixes the
        // motive universe to zero and exposes only the inductive's uparams.
        let (elim_level, rec_uparams) = if allows_large_elimination {
            let elim_param = self.fresh_elim_param(uparams);
            let elim_level = self.level_param(elim_param);
            let mut rec_uparams = Vec::with_capacity(uparams.len() + 1);
            rec_uparams.push(elim_param);
            rec_uparams.extend_from_slice(uparams);
            (elim_level, rec_uparams)
        } else {
            (self.level_zero(), uparams.to_vec())
        };
        let elim_sort = self.sort(elim_level);

        // We work in one shared local context: params, then motive, then the
        // minors. The fields for each constructor live in nested contexts during
        // minor and rec-rule construction.
        let mut ctx = LocalContext::new();

        // Open the parameter locals `p_1…p_m` and then the **index** locals
        // `idx_1…idx_k` (the recursor's canonical shared indices) from the
        // inductive's declared type telescope, with fresh fvars shared across the
        // whole recursor.
        let (params, rec_indices) =
            self.open_rec_params_and_indices(&mut ctx, num_params, num_indices, ind_ty);

        // `I p_1…p_m` (parameters threaded), the partial application used as the
        // motive-domain / major head before the indices are applied.
        let ind_applied_params = {
            let mut app = ind_const;
            for p in &params {
                let fv = self.fvar(p.fvar);
                app = self.app(app, fv);
            }
            app
        };
        // `I p_1…p_m idx_1…idx_k` (parameters AND the recursor's shared indices
        // threaded), used for the major's type and the motive's last domain.
        let ind_applied = {
            let mut app = ind_applied_params;
            for ix in &rec_indices {
                let fv = self.fvar(ix.fvar);
                app = self.app(app, fv);
            }
            app
        };
        let param_values: Vec<ExprId> = params.iter().map(|p| self.fvar(p.fvar)).collect();

        // motive : Π (idx_1…idx_k), (I p… idx…) → Sort v   (implicit). For a
        // non-indexed family this is the plain arrow `(I p…) → Sort v`.
        let motive_ty = {
            // Innermost: Π (_ : I p… idx…), Sort v.
            let anon = self.anon();
            let arrow = self.pi(anon, ind_applied, elim_sort, BinderInfo::Default);
            // Wrap the index telescope around it (abstracting the index fvars).
            self.abstr_pi_telescope(&rec_indices, arrow)
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
            let (fields, ctor_result) = self.open_ctor_fields(&mut ctx, num_params, &params, c);
            // The constructor's own index argument expressions, freshly in terms
            // of the just-opened field fvars (the crux of the indexed minor).
            let ctor_index_args = self.ctor_index_args(ctor_result, num_indices);
            // c_i p_1…p_m fields…  :  I p_1…p_m ctor_index_args…
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
            // motive <ctor's index exprs> (c_i p_1…p_m fields…) — the motive is
            // applied to the CONSTRUCTOR'S own index expressions, then the
            // constructor application.
            let motive_app = {
                let mut app = motive;
                for &ix in &ctor_index_args {
                    app = self.app(app, ix);
                }
                self.app(app, ctor_app)
            };
            // One induction-hypothesis binder `ih_j : motive f_j` per recursive
            // field `f_j`, in field order, opened *after* the field binders so
            // each IH's type references the already-bound field fvar.
            let ih_locals = self.open_ih_locals(
                &mut ctx,
                ind_name,
                ind_const,
                num_indices,
                &param_values,
                c,
                motive,
                &fields,
            )?;
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

        // major : I p_1…p_m idx_1…idx_k   (the recursor's shared indices).
        let major_fvar = ctx.fresh_fvar();
        let major_name = self.name_str_anon("t");
        let major_decl = LocalDecl {
            fvar: major_fvar,
            name: major_name,
            ty: ind_applied,
            info: BinderInfo::Default,
        };
        let major = self.fvar(major_fvar);

        // The result type `motive idx_1…idx_k major` (the motive applied to the
        // recursor's shared indices then the major), abstracted over the major,
        // the indices, the minors, the motive, and the params (params outermost —
        // the Lean convention: params before motive, indices before the major).
        let motive_major = {
            let mut app = motive;
            for ix in &rec_indices {
                let fv = self.fvar(ix.fvar);
                app = self.app(app, fv);
            }
            self.app(app, major)
        };
        let rec_ty = self.abstr_pi_telescope(&[major_decl], motive_major);
        let rec_ty = self.abstr_pi_telescope(&rec_indices, rec_ty);
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
            for &recursive_field in &c.recursive_fields {
                let opened = self.reopen_recursive_field(
                    ind_name,
                    ind_const,
                    num_indices,
                    &param_values,
                    c.name,
                    recursive_field,
                    fields,
                    &mut ctx,
                )?;
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
                for &index in &opened.indices {
                    rec_call = self.app(rec_call, index);
                }
                let Some(applied_value) = opened.applied_value else {
                    return Err(KernelError::RecursiveFieldShapeMismatch {
                        inductive: ind_name,
                        ctor: c.name,
                        field_index: u32::try_from(recursive_field.field_index).unwrap_or(u32::MAX),
                    });
                };
                rec_call = self.app(rec_call, applied_value);
                rec_call = self.abstr_lambda_telescope(&opened.telescope, rec_call);
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
            num_indices: u16::try_from(num_indices).expect("index count fits u16"),
        })
    }

    /// Open the recursor's `num_params` parameter locals followed by its
    /// `num_indices` index locals into `ctx` (pushing each), with their types
    /// read from the inductive's declared type telescope `ind_ty`. Returns
    /// `(params, indices)`, each outer-to-inner. Every telescope type is
    /// instantiated with the preceding fvars so later types (including index
    /// types) see the earlier params/indices.
    fn open_rec_params_and_indices(
        &mut self,
        ctx: &mut LocalContext,
        num_params: usize,
        num_indices: usize,
        ind_ty: ExprId,
    ) -> (Vec<LocalDecl>, Vec<LocalDecl>) {
        let mut params = Vec::with_capacity(num_params);
        let mut indices = Vec::with_capacity(num_indices);
        let mut cursor = self.whnf(ind_ty);
        for i in 0..(num_params + num_indices) {
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
            if i < num_params {
                params.push(decl);
            } else {
                indices.push(decl);
            }
            let fv = self.fvar(fvar);
            cursor = self.instantiate(body, &[fv]);
            cursor = self.whnf(cursor);
        }
        (params, indices)
    }

    /// `Const(c, [Param(u)…])` for a constructor sharing the inductive's
    /// universe parameters.
    fn mk_ind_const_for_ctor(&mut self, ctor_name: NameId, uparams: &[NameId]) -> ExprId {
        let levels = uparams.iter().map(|&u| self.level_param(u)).collect();
        self.const_(ctor_name, levels)
    }

    /// Open a constructor's **field** telescope into fresh locals in `ctx`
    /// (pushing each), returning them outer-to-inner together with the
    /// constructor's **result tail** `I params idx_1…idx_k` instantiated in
    /// terms of the recursor's shared parameter fvars and these fresh field
    /// fvars (so the caller can extract the constructor's index argument
    /// expressions freshly). The constructor's leading `num_params` parameter
    /// binders are first skipped, instantiating them with the recursor's
    /// parameter fvars (`params`); later field types are instantiated as we go
    /// so they see earlier fields as their fvars.
    fn open_ctor_fields(
        &mut self,
        ctx: &mut LocalContext,
        num_params: usize,
        params: &[LocalDecl],
        c: &CheckedCtor,
    ) -> (Vec<LocalDecl>, ExprId) {
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
        (fields, cursor)
    }

    /// Extract a constructor's `num_indices` **index argument expressions** from
    /// its (already field-instantiated) result tail `I params idx_1…idx_k`: the
    /// trailing `num_indices` arguments of the spine, in natural order. The
    /// leading `num_params` args are the parameters and are dropped.
    fn ctor_index_args(&self, result_tail: ExprId, num_indices: usize) -> Vec<ExprId> {
        if num_indices == 0 {
            return Vec::new();
        }
        let (_head, args) = self.unfold_apps(result_tail);
        // The spine is `params… idx…`; the last `num_indices` args are the
        // indices (the check in `check_ctor` guarantees the arity).
        let start = args.len().saturating_sub(num_indices);
        args[start..].to_vec()
    }

    /// Open one induction-hypothesis local per checked recursive field, in field
    /// order. Each IH type is rederived from the field's WHNF telescope tail by
    /// the same helper used during constructor classification. Returns the IH
    /// locals outer-to-inner.
    #[allow(clippy::too_many_arguments)]
    fn open_ih_locals(
        &mut self,
        ctx: &mut LocalContext,
        ind_name: NameId,
        ind_const: ExprId,
        num_indices: usize,
        param_values: &[ExprId],
        ctor: &CheckedCtor,
        motive: ExprId,
        fields: &[LocalDecl],
    ) -> Result<Vec<LocalDecl>, KernelError> {
        let mut ihs = Vec::with_capacity(ctor.recursive_fields.len());
        for &recursive_field in &ctor.recursive_fields {
            let opened = self.reopen_recursive_field(
                ind_name,
                ind_const,
                num_indices,
                param_values,
                ctor.name,
                recursive_field,
                fields,
                ctx,
            )?;
            let mut ih_body = motive;
            for &index in &opened.indices {
                ih_body = self.app(ih_body, index);
            }
            let Some(applied_value) = opened.applied_value else {
                return Err(KernelError::RecursiveFieldShapeMismatch {
                    inductive: ind_name,
                    ctor: ctor.name,
                    field_index: u32::try_from(recursive_field.field_index).unwrap_or(u32::MAX),
                });
            };
            ih_body = self.app(ih_body, applied_value);
            let ih_ty = self.abstr_pi_telescope(&opened.telescope, ih_body);
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
        Ok(ihs)
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
    /// nanoda's `reduce_rec`, for the parametric, **indexed** scope: parameters
    /// are consumed by both the recursor application and the constructor
    /// application (and threaded into recursive calls by the rule value), while
    /// the recursor's **index arguments** sit at `args[prefix_len..major_idx]`
    /// (between the minors and the major) and are **dropped** — the rule value's
    /// λ-telescope binds `params motive minors fields…`, never the indices, so
    /// the major's actual indices need not be re-supplied.
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
        let major = self.nat_literal_to_constructor(major).unwrap_or(major);
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
