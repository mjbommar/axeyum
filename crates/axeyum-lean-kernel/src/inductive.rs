//! The inductive layer (ADR-0036, slice 7): the trusted [`Kernel::add_inductive`]
//! admission gate, recursor generation (with induction hypotheses, parameters,
//! and **indices**), and ι-reduction in WHNF.
//!
//! ## Scope — parametric, indexed, and mutual recursive groups
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
//! A field is recursive when WHNF opens a possibly empty `Pi` telescope whose
//! tail is exactly `I p_1…p_m idx_1…idx_k`. Its induction hypothesis preserves
//! that telescope and applies the terminal family's motive to the recursive
//! occurrence's own indices and fully applied field value. Empty telescopes and
//! indices recover the historical direct case; nonempty indices and telescopes
//! cover `Vector`- and `Acc`-shaped recursion. TL2.13 M2 generalizes this one
//! rule to an ordered mutual group: positivity ranges over every family, every
//! recursor binds all motives and minors, and each recursive field selects the
//! motive and recursor of its terminal family. Singleton admission is a wrapper
//! over the same atomic implementation.
//!
//! Still deferred (and rejected explicitly, never guessed): nested occurrences
//! under a foreign type constructor, malformed family applications, and
//! frontend lowering for well-founded/nested definitions.
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
//!   induction-hypothesis binder per recursive field `f_j`** (in field order).
//!   For `f_j : Pi xs, I p… indices`, that binder has type
//!   `Pi xs, motive indices (f_j xs)`. The parameters are threaded into both
//!   the constructor application and recursive motive applications.
//! - one [`RecRule`] per constructor, with
//!   `value = λ params motive m_1 … m_n (fields_i…),
//!            m_i fields_i… (I.rec params motive m… f_j)…`
//!   — the ι-RHS applies the minor to the fields and then to one recursive call
//!   `fun xs => I.rec params motive minors… indices (f_j xs)` per recursive
//!   field `f_j` (with empty lambdas/indices in the direct case).
//!
//! The generated recursor's type is itself `infer`-checked (a self-check):
//! a wrong recursor (e.g. a mis-indexed induction hypothesis or a mis-threaded
//! parameter) would wrongly accept proofs, so it is verified rather than
//! trusted.

use std::collections::BTreeSet;

use crate::env::{Declaration, RecRule};
use crate::expr::{ExprId, ExprNode};
use crate::name::NameId;
use crate::tc::{KernelError, LocalContext, LocalDecl};
use crate::{BinderInfo, Kernel};

/// One family in an explicitly ordered mutual-inductive group.
///
/// The group-level universe parameters and parameter count are supplied once to
/// [`Kernel::add_mutual_inductive`]. Each family owns its closed type and its
/// constructors in declaration order. Persistent group metadata is deliberately
/// absent: TL2.13 reconstructs and checks the group transactionally rather than
/// changing declaration-identity v1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveFamilySpec {
    /// The inductive type's declaration name.
    pub name: NameId,
    /// The inductive type's closed parameter/index telescope.
    pub ty: ExprId,
    /// Constructor names and closed types in declaration order.
    pub constructors: Vec<(NameId, ExprId)>,
}

impl InductiveFamilySpec {
    /// Construct one owned family specification.
    #[must_use]
    pub fn new(name: NameId, ty: ExprId, constructors: Vec<(NameId, ExprId)>) -> Self {
        Self {
            name,
            ty,
            constructors,
        }
    }
}

/// Family facts checked before any constructor is admitted.
struct CheckedFamily {
    name: NameId,
    ty: ExprId,
    num_indices: usize,
    ind_const: ExprId,
    constructors: Vec<CheckedCtor>,
}

/// One checked group shares the first family's parameter locals and result
/// universe. Constructor and recursor generation consume this representation;
/// no parallel family/name/index vectors may drift apart.
struct CheckedInductiveGroup {
    params: Vec<LocalDecl>,
    result_level: crate::LevelId,
    families: Vec<CheckedFamily>,
}

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
    ///    `I`) or may WHNF to a possibly empty `Pi` telescope ending in the exact
    ///    family application `I p_1…p_m idx_1…idx_k`. Fixed parameters, complete
    ///    index arity, occurrence-free indices, and positivity are mandatory.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError::DeclarationExists`] for a duplicate name,
    /// [`KernelError::InductiveTypeNotASort`] if `ty`'s param+index-stripped tail
    /// is not a `Sort`, [`KernelError::NonPositiveInductiveOccurrence`] for a family occurrence
    /// in a function domain, [`KernelError::InvalidInductiveOccurrence`] for a
    /// containing term that is not a valid family application,
    /// [`KernelError::ReflexiveOrNestedNotSupported`] for an unsupported nested
    /// occurrence, [`KernelError::RecursiveInductiveNotSupported`] for an
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
        let family = InductiveFamilySpec::new(name, ty, ctors.to_vec());
        self.add_mutual_inductive(uparams, num_params, &[family])
    }

    /// Type-check and atomically admit an explicitly ordered inductive group.
    ///
    /// TL2.13 M2 checks and admits the complete group through one trusted path:
    /// common parameters/universe, complete-group positivity, all family and
    /// constructor declarations, globally ordered motives/minors, one recursor
    /// per family, and all-or-nothing publication. A singleton follows this
    /// same implementation while retaining its established declarations,
    /// computations, identities, and error payloads.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError::EmptyInductiveGroup`] for no families,
    /// [`KernelError::DuplicateInductiveGroupName`] for group-local name
    /// collisions, [`KernelError::MutualInductiveParameterMismatch`] for a
    /// non-shared parameter telescope,
    /// [`KernelError::MutualInductiveResultUniverseMismatch`] for inequivalent
    /// family result universes, [`KernelError::DeclarationExists`] for an
    /// environment collision, or any constructor/positivity/recursor error
    /// surfaced by the atomic trusted gate. Singleton inputs retain every error
    /// from [`Kernel::add_inductive`]'s historical trusted gate.
    pub fn add_mutual_inductive(
        &mut self,
        uparams: &[NameId],
        num_params: usize,
        families: &[InductiveFamilySpec],
    ) -> Result<(), KernelError> {
        if families.is_empty() {
            return Err(KernelError::EmptyInductiveGroup);
        }
        self.with_inductive_transaction(|kernel| {
            kernel.add_inductive_group(uparams, num_params, families)
        })
    }

    /// Execute one inductive admission attempt against an insertion checkpoint.
    /// Failed provisional declarations and environment-sensitive caches never
    /// escape the transaction. Checkpoint and rollback cost scale with the
    /// attempted group, not the complete prior environment. Expression/name
    /// interning remains monotone and deterministic, as elsewhere in the kernel.
    fn with_inductive_transaction<T>(
        &mut self,
        action: impl FnOnce(&mut Self) -> Result<T, KernelError>,
    ) -> Result<T, KernelError> {
        let checkpoint = self.env.checkpoint();
        match action(self) {
            Ok(value) => Ok(value),
            Err(error) => {
                self.env.rollback_unchecked(checkpoint);
                self.infer_closed_cache.clear();
                self.whnf_cache.clear();
                Err(error)
            }
        }
    }

    /// Check the family facts that precede complete-group positivity and any
    /// provisional declaration insertion.
    fn check_mutual_inductive_preflight(
        &mut self,
        uparams: &[NameId],
        num_params: usize,
        families: &[InductiveFamilySpec],
    ) -> Result<CheckedInductiveGroup, KernelError> {
        let mut names = BTreeSet::new();
        let singleton = families.len() == 1;
        for family in families {
            self.check_group_name(family.name, &mut names, singleton)?;
            for &(constructor, _) in &family.constructors {
                self.check_group_name(constructor, &mut names, singleton)?;
            }
            let recursor = self.name_str(family.name, "rec");
            self.check_group_name(recursor, &mut names, singleton)?;
        }

        let mut shared_parameters = Vec::with_capacity(num_params);
        let mut shared_result_level = None;
        let mut checked_families = Vec::with_capacity(families.len());
        for (family_index, family) in families.iter().enumerate() {
            let (num_indices, result_level) = self.check_mutual_family_type(
                family,
                family_index,
                num_params,
                &mut shared_parameters,
                singleton,
            )?;
            if let Some(expected) = shared_result_level {
                if !self.level_is_equiv(expected, result_level) {
                    return Err(KernelError::MutualInductiveResultUniverseMismatch {
                        family: family.name,
                    });
                }
            } else {
                shared_result_level = Some(result_level);
            }
            checked_families.push(CheckedFamily {
                name: family.name,
                ty: family.ty,
                num_indices,
                ind_const: self.mk_ind_const(family.name, uparams),
                constructors: Vec::new(),
            });
        }
        Ok(CheckedInductiveGroup {
            params: shared_parameters,
            result_level: shared_result_level.expect("a nonempty group has a result universe"),
            families: checked_families,
        })
    }

    fn check_group_name(
        &self,
        name: NameId,
        group_names: &mut BTreeSet<NameId>,
        singleton: bool,
    ) -> Result<(), KernelError> {
        if self.env.contains(name) {
            return Err(KernelError::DeclarationExists { name });
        }
        if !group_names.insert(name) && !singleton {
            return Err(KernelError::DuplicateInductiveGroupName { name });
        }
        Ok(())
    }

    /// Open one family against the first family's shared parameter locals and
    /// return its result-universe level after independently opening its indices.
    fn check_mutual_family_type(
        &mut self,
        family: &InductiveFamilySpec,
        family_index: usize,
        num_params: usize,
        shared_parameters: &mut Vec<LocalDecl>,
        singleton: bool,
    ) -> Result<(usize, crate::LevelId), KernelError> {
        let mut ctx = LocalContext::new();
        if family_index != 0 {
            for parameter in shared_parameters.iter().copied() {
                ctx.bump_fresh_above(parameter.fvar);
                ctx.push(parameter);
            }
        }

        let inferred = self.infer_core(family.ty, &mut ctx)?;
        let inferred = self.whnf(inferred);
        if !matches!(self.expr_node(inferred), ExprNode::Sort(_)) {
            return Err(KernelError::InductiveTypeNotASort { got: inferred });
        }

        let mut cursor = self.whnf(family.ty);
        for parameter_index in 0..num_params {
            let ExprNode::Pi(name, domain, body, info) = self.expr_node(cursor).clone() else {
                if singleton {
                    return Err(KernelError::InductiveTypeNotASort { got: cursor });
                }
                return Err(KernelError::MutualInductiveParameterMismatch {
                    family: family.name,
                    parameter_index,
                });
            };
            let parameter = if family_index == 0 {
                let parameter = LocalDecl {
                    fvar: ctx.fresh_fvar(),
                    name,
                    ty: domain,
                    info,
                };
                ctx.push(parameter);
                shared_parameters.push(parameter);
                parameter
            } else {
                let parameter = shared_parameters[parameter_index];
                if !self.def_eq_in(domain, parameter.ty, &mut ctx) {
                    return Err(KernelError::MutualInductiveParameterMismatch {
                        family: family.name,
                        parameter_index,
                    });
                }
                parameter
            };
            let value = self.fvar(parameter.fvar);
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
        }

        let mut num_indices = 0;
        while let ExprNode::Pi(name, domain, body, info) = self.expr_node(cursor).clone() {
            let index = LocalDecl {
                fvar: ctx.fresh_fvar(),
                name,
                ty: domain,
                info,
            };
            ctx.push(index);
            let value = self.fvar(index.fvar);
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
            num_indices += 1;
        }
        let ExprNode::Sort(result_level) = self.expr_node(cursor) else {
            return Err(KernelError::InductiveTypeNotASort { got: cursor });
        };
        Ok((num_indices, *result_level))
    }

    /// Admit one already ordered family group. All inserts in this method are
    /// provisional until [`Kernel::with_inductive_transaction`] returns `Ok`.
    #[allow(clippy::too_many_lines)]
    fn add_inductive_group(
        &mut self,
        uparams: &[NameId],
        num_params: usize,
        families: &[InductiveFamilySpec],
    ) -> Result<(), KernelError> {
        let mut group = self.check_mutual_inductive_preflight(uparams, num_params, families)?;

        // Positivity sees every family before any header is visible. This is
        // the decisive difference from repeated single-family admission.
        for (owner_index, family) in families.iter().enumerate() {
            for &(constructor, ty) in &family.constructors {
                self.check_group_constructor_positivity(
                    &group,
                    owner_index,
                    num_params,
                    constructor,
                    ty,
                )?;
            }
        }

        // All family constants must resolve while constructor types are
        // checked. The aggregate recursive bit is corrected after trusted
        // field classification and is group-wide, matching Lean's `is_rec`.
        for (family, spec) in group.families.iter().zip(families) {
            self.env.insert_unchecked(Declaration::Inductive {
                name: family.name,
                uparams: uparams.to_vec(),
                ty: family.ty,
                num_params: u16::try_from(num_params).expect("parameter count fits u16"),
                num_indices: u16::try_from(family.num_indices).expect("index count fits u16"),
                is_recursive: false,
                ctor_names: spec.constructors.iter().map(|(name, _)| *name).collect(),
            });
        }

        for (owner_index, spec) in families.iter().enumerate() {
            let mut checked = Vec::with_capacity(spec.constructors.len());
            for (constructor_index, &(name, ty)) in spec.constructors.iter().enumerate() {
                let (fields, recursive_fields, exposes_non_prop_fields) =
                    self.check_group_ctor(&group, owner_index, num_params, name, ty)?;
                checked.push(CheckedCtor {
                    name,
                    ty,
                    idx: u16::try_from(constructor_index).expect("constructor count fits u16"),
                    fields,
                    recursive_fields,
                    exposes_non_prop_fields,
                });
            }
            group.families[owner_index].constructors = checked;
        }

        let is_recursive = group.families.iter().any(|family| {
            family
                .constructors
                .iter()
                .any(|constructor| !constructor.recursive_fields.is_empty())
        });
        for (family, spec) in group.families.iter().zip(families) {
            self.env.insert_unchecked(Declaration::Inductive {
                name: family.name,
                uparams: uparams.to_vec(),
                ty: family.ty,
                num_params: u16::try_from(num_params).expect("parameter count fits u16"),
                num_indices: u16::try_from(family.num_indices).expect("index count fits u16"),
                is_recursive,
                ctor_names: spec.constructors.iter().map(|(name, _)| *name).collect(),
            });
        }

        for family in &group.families {
            for constructor in &family.constructors {
                self.env.insert_unchecked(Declaration::Constructor {
                    name: constructor.name,
                    uparams: uparams.to_vec(),
                    ty: constructor.ty,
                    inductive: family.name,
                    idx: constructor.idx,
                    num_fields: u16::try_from(constructor.fields.len())
                        .expect("field count fits u16"),
                });
            }
        }

        let allows_large_elimination = self.level_is_nonzero(group.result_level)
            || (group.families.len() == 1
                && match group.families[0].constructors.as_slice() {
                    [] => true,
                    [constructor] => constructor.exposes_non_prop_fields,
                    _ => false,
                });
        let recursors =
            self.mk_group_recursors(uparams, num_params, &group, allows_large_elimination)?;
        self.validate_group_recursor_contract(num_params, &group, &recursors)?;
        for recursor in &recursors {
            self.env.insert_unchecked(recursor.clone());
        }
        self.check_group_recursor_rules(&recursors)?;
        Ok(())
    }

    /// Recheck the non-expression metadata generated for each owner family.
    /// Expression-level type/rule checking is separate so mutations of either
    /// layer cannot hide behind the other.
    fn validate_group_recursor_contract(
        &mut self,
        num_params: usize,
        group: &CheckedInductiveGroup,
        recursors: &[Declaration],
    ) -> Result<(), KernelError> {
        let total_minors: usize = group
            .families
            .iter()
            .map(|family| family.constructors.len())
            .sum();
        if recursors.len() != group.families.len() {
            return Err(KernelError::MutualRecursorContractMismatch {
                family: group.families[0].name,
            });
        }
        for (family, recursor) in group.families.iter().zip(recursors) {
            let expected_name = self.name_str(family.name, "rec");
            let Declaration::Recursor {
                name,
                rec_rules,
                num_motives,
                num_minors,
                num_params: actual_params,
                num_indices,
                ..
            } = recursor
            else {
                return Err(KernelError::MutualRecursorContractMismatch {
                    family: family.name,
                });
            };
            let metadata_matches = *name == expected_name
                && usize::from(*num_motives) == group.families.len()
                && usize::from(*num_minors) == total_minors
                && usize::from(*actual_params) == num_params
                && usize::from(*num_indices) == family.num_indices
                && rec_rules.len() == family.constructors.len()
                && rec_rules
                    .iter()
                    .zip(&family.constructors)
                    .all(|(rule, constructor)| {
                        rule.ctor_name == constructor.name
                            && usize::from(rule.num_fields) == constructor.fields.len()
                    });
            if !metadata_matches {
                return Err(KernelError::MutualRecursorContractMismatch {
                    family: family.name,
                });
            }
        }
        Ok(())
    }

    /// Check every closed computation-rule value only after all group recursor
    /// constants are provisionally visible. Cross-family calls therefore pass
    /// through ordinary kernel inference instead of receiving a special trust
    /// exemption. Any failure is rolled back by the enclosing transaction.
    fn check_group_recursor_rules(&mut self, recursors: &[Declaration]) -> Result<(), KernelError> {
        for recursor in recursors {
            let Declaration::Recursor { rec_rules, .. } = recursor else {
                unreachable!("group recursor generation returns only recursors");
            };
            for rule in rec_rules {
                let mut ctx = LocalContext::new();
                let _ = self.infer_core(rule.value, &mut ctx)?;
            }
        }
        Ok(())
    }

    /// Build a group family constant with the declaration's universe parameters.
    fn mk_ind_const(&mut self, name: NameId, uparams: &[NameId]) -> ExprId {
        let levels = uparams.iter().map(|&u| self.level_param(u)).collect();
        self.const_(name, levels)
    }

    /// Check every field in one constructor against the complete group
    /// occurrence set before any family header is inserted.
    fn check_group_constructor_positivity(
        &mut self,
        group: &CheckedInductiveGroup,
        owner_index: usize,
        num_params: usize,
        ctor_name: NameId,
        ctor_ty: ExprId,
    ) -> Result<(), KernelError> {
        let mut ctx = LocalContext::new();
        let mut param_values = Vec::with_capacity(num_params);
        for parameter in group.params.iter().take(num_params) {
            ctx.bump_fresh_above(parameter.fvar);
            ctx.push(*parameter);
            param_values.push(self.fvar(parameter.fvar));
        }

        let mut cursor = self.whnf(ctor_ty);
        for &parameter in &param_values {
            let ExprNode::Pi(_, _, body, _) = self.expr_node(cursor).clone() else {
                // The constructor checker retains authority for malformed
                // parameter telescopes and their historical error payloads.
                return Ok(());
            };
            cursor = self.instantiate(body, &[parameter]);
            cursor = self.whnf(cursor);
        }

        let mut field_index = 0_u32;
        while let ExprNode::Pi(name, domain, body, info) = self.expr_node(cursor).clone() {
            self.check_group_positive_occurrence(
                group,
                owner_index,
                &param_values,
                ctor_name,
                field_index,
                domain,
                &mut ctx,
            )?;
            let fvar = ctx.fresh_fvar();
            ctx.push(LocalDecl {
                fvar,
                name,
                ty: domain,
                info,
            });
            let value = self.fvar(fvar);
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
            field_index = field_index
                .checked_add(1)
                .ok_or(KernelError::MalformedConstructorType { ctor: ctor_name })?;
        }
        Ok(())
    }

    /// Pinned Lean 4.30 positivity over one complete mutual family set.
    #[allow(clippy::too_many_arguments)]
    fn check_group_positive_occurrence(
        &mut self,
        group: &CheckedInductiveGroup,
        owner_index: usize,
        param_values: &[ExprId],
        ctor_name: NameId,
        field_index: u32,
        term: ExprId,
        ctx: &mut LocalContext,
    ) -> Result<(), KernelError> {
        let term = self.whnf(term);
        if !self.mentions_group_family(term, group) {
            return Ok(());
        }

        if let ExprNode::Pi(name, domain, body, info) = self.expr_node(term).clone() {
            if self.mentions_group_family(domain, group) {
                return Err(KernelError::NonPositiveInductiveOccurrence {
                    inductive: group.families[owner_index].name,
                    ctor: ctor_name,
                    field_index,
                });
            }
            let fvar = ctx.fresh_fvar();
            ctx.push(LocalDecl {
                fvar,
                name,
                ty: domain,
                info,
            });
            let value = self.fvar(fvar);
            let body = self.instantiate(body, &[value]);
            let result = self.check_group_positive_occurrence(
                group,
                owner_index,
                param_values,
                ctor_name,
                field_index,
                body,
                ctx,
            );
            ctx.pop();
            return result;
        }

        if self
            .valid_group_family_application(term, group, param_values)
            .is_some()
        {
            return Ok(());
        }

        Err(KernelError::InvalidInductiveOccurrence {
            inductive: group.families[owner_index].name,
            ctor: ctor_name,
            field_index,
        })
    }

    /// Return the target family for an exact `I_j params indices` application.
    fn valid_group_family_application(
        &self,
        term: ExprId,
        group: &CheckedInductiveGroup,
        param_values: &[ExprId],
    ) -> Option<usize> {
        let (head, args) = self.unfold_apps(term);
        group.families.iter().position(|family| {
            head == family.ind_const
                && args.len() == param_values.len() + family.num_indices
                && args[..param_values.len()] == param_values[..]
                && args[param_values.len()..]
                    .iter()
                    .all(|&index| !self.mentions_group_family(index, group))
        })
    }

    /// Whether any family constant in `group` occurs structurally in `term`.
    fn mentions_group_family(&self, term: ExprId, group: &CheckedInductiveGroup) -> bool {
        match self.expr_node(term).clone() {
            ExprNode::Const(name, _) => group.families.iter().any(|family| family.name == name),
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => false,
            ExprNode::Proj(_, _, structure) => self.mentions_group_family(structure, group),
            ExprNode::App(function, argument) => {
                self.mentions_group_family(function, group)
                    || self.mentions_group_family(argument, group)
            }
            ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
                self.mentions_group_family(ty, group) || self.mentions_group_family(body, group)
            }
            ExprNode::Let(_, ty, value, body) => {
                self.mentions_group_family(ty, group)
                    || self.mentions_group_family(value, group)
                    || self.mentions_group_family(body, group)
            }
        }
    }

    /// Check one constructor against its owner family and classify recursive
    /// fields against every family in the group.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn check_group_ctor(
        &mut self,
        group: &CheckedInductiveGroup,
        owner_index: usize,
        num_params: usize,
        ctor_name: NameId,
        ctor_ty: ExprId,
    ) -> Result<(Vec<LocalDecl>, Vec<RecursiveField>, bool), KernelError> {
        let owner = &group.families[owner_index];
        let mut ctx = LocalContext::new();
        for parameter in group.params.iter().take(num_params) {
            ctx.push(*parameter);
            ctx.bump_fresh_above(parameter.fvar);
        }

        let inferred = self.infer_core(ctor_ty, &mut ctx)?;
        let inferred = self.whnf(inferred);
        if !matches!(self.expr_node(inferred), ExprNode::Sort(_)) {
            return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
        }

        let mut cursor = self.whnf(ctor_ty);
        let parameters: Vec<_> = group.params.iter().take(num_params).copied().collect();
        for parameter in &parameters {
            let ExprNode::Pi(_, domain, body, _) = self.expr_node(cursor).clone() else {
                return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
            };
            if !self.def_eq(domain, parameter.ty) {
                return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
            }
            let value = self.fvar(parameter.fvar);
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
        }

        let param_values: Vec<_> = parameters
            .iter()
            .map(|parameter| self.fvar(parameter.fvar))
            .collect();
        let mut fields = Vec::new();
        let mut recursive_fields = Vec::new();
        let mut non_prop_field_values = Vec::new();
        while let ExprNode::Pi(name, domain, body, info) = self.expr_node(cursor).clone() {
            let domain_type = self.infer_core(domain, &mut ctx)?;
            let domain_type = self.whnf(domain_type);
            let ExprNode::Sort(domain_level) = self.expr_node(domain_type) else {
                return Err(KernelError::MalformedConstructorType { ctor: ctor_name });
            };
            let field_is_proof = self.level_is_zero(*domain_level);

            if let Some((target_family, opened)) =
                self.open_group_recursive_field_shape(group, &param_values, domain, None, &mut ctx)
            {
                recursive_fields.push(RecursiveField {
                    field_index: fields.len(),
                    target_family,
                    telescope_depth: opened.telescope.len(),
                });
            } else if self.mentions_group_family(domain, group) {
                return Err(self.classify_bad_group_recursive_field(
                    group,
                    owner_index,
                    ctor_name,
                    domain,
                ));
            }

            let fvar = ctx.fresh_fvar();
            let field = LocalDecl {
                fvar,
                name,
                ty: domain,
                info,
            };
            ctx.push(field);
            fields.push(field);
            let value = self.fvar(fvar);
            if !field_is_proof {
                non_prop_field_values.push(value);
            }
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
        }

        let (head, args) = self.unfold_apps(cursor);
        if head != owner.ind_const || args.len() != num_params + owner.num_indices {
            return Err(KernelError::ConstructorResultMismatch {
                expected: owner.name,
                ctor: ctor_name,
            });
        }
        for (index, parameter) in parameters.iter().enumerate() {
            if args[index] != self.fvar(parameter.fvar) {
                return Err(KernelError::ConstructorResultMismatch {
                    expected: owner.name,
                    ctor: ctor_name,
                });
            }
        }
        let exposes_non_prop_fields = non_prop_field_values
            .iter()
            .all(|field| args.contains(field));
        Ok((fields, recursive_fields, exposes_non_prop_fields))
    }

    /// Open a possibly higher-order recursive field and select the family at
    /// its terminal exact application.
    fn open_group_recursive_field_shape(
        &mut self,
        group: &CheckedInductiveGroup,
        param_values: &[ExprId],
        field_ty: ExprId,
        recursive_value: Option<ExprId>,
        ctx: &mut LocalContext,
    ) -> Option<(usize, OpenedRecursiveField)> {
        let mut cursor = self.whnf(field_ty);
        let mut telescope = Vec::new();
        let mut applied_value = recursive_value;
        let mut valid_domains = true;
        while let ExprNode::Pi(name, domain, body, info) = self.expr_node(cursor).clone() {
            if self.mentions_group_family(domain, group) {
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

        let target = if valid_domains {
            self.valid_group_family_application(cursor, group, param_values)
        } else {
            None
        };
        let indices = target.map(|_| {
            let (_, args) = self.unfold_apps(cursor);
            args[param_values.len()..].to_vec()
        });
        for _ in 0..telescope.len() {
            ctx.pop();
        }
        let target = target?;
        Some((
            target,
            OpenedRecursiveField {
                telescope,
                indices: indices.expect("a valid target has an index suffix"),
                applied_value,
            },
        ))
    }

    /// Reopen a checked recursive descriptor in a recursor-local context.
    #[allow(clippy::too_many_arguments)]
    fn reopen_group_recursive_field(
        &mut self,
        group: &CheckedInductiveGroup,
        param_values: &[ExprId],
        owner_index: usize,
        ctor_name: NameId,
        descriptor: RecursiveField,
        fields: &[LocalDecl],
        ctx: &mut LocalContext,
    ) -> Result<OpenedRecursiveField, KernelError> {
        let field_index = u32::try_from(descriptor.field_index).unwrap_or(u32::MAX);
        let Some(field) = fields.get(descriptor.field_index).copied() else {
            return Err(KernelError::RecursiveFieldShapeMismatch {
                inductive: group.families[owner_index].name,
                ctor: ctor_name,
                field_index,
            });
        };
        let value = self.fvar(field.fvar);
        let Some((target, opened)) =
            self.open_group_recursive_field_shape(group, param_values, field.ty, Some(value), ctx)
        else {
            return Err(KernelError::RecursiveFieldShapeMismatch {
                inductive: group.families[owner_index].name,
                ctor: ctor_name,
                field_index,
            });
        };
        if target != descriptor.target_family
            || opened.telescope.len() != descriptor.telescope_depth
            || opened.applied_value.is_none()
        {
            return Err(KernelError::RecursiveFieldShapeMismatch {
                inductive: group.families[owner_index].name,
                ctor: ctor_name,
                field_index,
            });
        }
        Ok(opened)
    }

    fn classify_bad_group_recursive_field(
        &self,
        group: &CheckedInductiveGroup,
        owner_index: usize,
        ctor_name: NameId,
        domain: ExprId,
    ) -> KernelError {
        let owner = group.families[owner_index].name;
        if matches!(self.expr_node(domain), ExprNode::Pi(..)) {
            return KernelError::ReflexiveOrNestedNotSupported {
                inductive: owner,
                ctor: ctor_name,
            };
        }
        let (head, args) = self.unfold_apps(domain);
        if !args.is_empty() && group.families.iter().any(|family| family.ind_const == head) {
            return KernelError::RecursiveInductiveNotSupported {
                inductive: owner,
                ctor: ctor_name,
            };
        }
        KernelError::ReflexiveOrNestedNotSupported {
            inductive: owner,
            ctor: ctor_name,
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
    /// position (within `fields`, parameters excluded). The descriptor retains
    /// only the field position and telescope depth; context-specific binders,
    /// indices, and applied values are rederived for each trusted use.
    /// One induction hypothesis (in the recursor's minor premise) and one
    /// recursive call (in the ι-rule) is generated per entry, in this order.
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
    target_family: usize,
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
    /// Generate all per-family recursors from one shared motive/minor context.
    /// The returned declarations are not published until every type self-checks.
    #[allow(clippy::too_many_lines)]
    fn mk_group_recursors(
        &mut self,
        uparams: &[NameId],
        num_params: usize,
        group: &CheckedInductiveGroup,
        allows_large_elimination: bool,
    ) -> Result<Vec<Declaration>, KernelError> {
        let (elim_level, rec_uparams) = if allows_large_elimination {
            let elim_param = self.fresh_elim_param(uparams);
            let mut rec_uparams = Vec::with_capacity(uparams.len() + 1);
            rec_uparams.push(elim_param);
            rec_uparams.extend_from_slice(uparams);
            (self.level_param(elim_param), rec_uparams)
        } else {
            (self.level_zero(), uparams.to_vec())
        };
        let elim_sort = self.sort(elim_level);
        let rec_level_args: Vec<_> = rec_uparams
            .iter()
            .map(|&parameter| self.level_param(parameter))
            .collect();

        let mut ctx = LocalContext::new();
        let params = self.open_group_params(&mut ctx, num_params, group.families[0].ty);
        let param_values: Vec<_> = params
            .iter()
            .map(|parameter| self.fvar(parameter.fvar))
            .collect();

        // Motives are global and ordered by family.
        let mut motives = Vec::with_capacity(group.families.len());
        for (family_index, family) in group.families.iter().enumerate() {
            let indices = self.open_group_indices(&mut ctx, num_params, &params, family);
            let family_app = self.apply_family(family.ind_const, &params, &indices);
            let anon = self.anon();
            let motive_result = self.pi(anon, family_app, elim_sort, BinderInfo::Default);
            let motive_ty = self.abstr_pi_telescope(&indices, motive_result);
            for _ in 0..indices.len() {
                ctx.pop();
            }
            let base_name = self.name_str_anon("motive");
            let name = if group.families.len() == 1 {
                base_name
            } else {
                self.name_num(base_name, (family_index + 1) as u64)
            };
            let motive = LocalDecl {
                fvar: ctx.fresh_fvar(),
                name,
                ty: motive_ty,
                info: BinderInfo::Implicit,
            };
            ctx.push(motive);
            motives.push(motive);
        }

        // Minors are global and ordered by family, then constructor.
        let total_minors: usize = group
            .families
            .iter()
            .map(|family| family.constructors.len())
            .sum();
        let mut minors = Vec::with_capacity(total_minors);
        let mut ctor_fields: Vec<Vec<Vec<LocalDecl>>> = group
            .families
            .iter()
            .map(|family| Vec::with_capacity(family.constructors.len()))
            .collect();
        for (owner_index, family) in group.families.iter().enumerate() {
            for constructor in &family.constructors {
                let (fields, result) =
                    self.open_ctor_fields(&mut ctx, num_params, &params, constructor);
                let result_indices = self.ctor_index_args(result, family.num_indices);
                let constructor_app = {
                    let mut app = self.mk_ind_const_for_ctor(constructor.name, uparams);
                    for parameter in &params {
                        let value = self.fvar(parameter.fvar);
                        app = self.app(app, value);
                    }
                    for field in &fields {
                        let value = self.fvar(field.fvar);
                        app = self.app(app, value);
                    }
                    app
                };
                let mut motive_app = self.fvar(motives[owner_index].fvar);
                for index in result_indices {
                    motive_app = self.app(motive_app, index);
                }
                motive_app = self.app(motive_app, constructor_app);

                let ihs = self.open_group_ih_locals(
                    &mut ctx,
                    group,
                    owner_index,
                    &param_values,
                    constructor,
                    &motives,
                    &fields,
                )?;
                let minor_body = self.abstr_pi_telescope(&ihs, motive_app);
                let minor_ty = self.abstr_pi_telescope(&fields, minor_body);
                for _ in 0..ihs.len() {
                    ctx.pop();
                }
                for _ in 0..fields.len() {
                    ctx.pop();
                }
                let minor = LocalDecl {
                    fvar: ctx.fresh_fvar(),
                    name: self.minor_name(constructor.name),
                    ty: minor_ty,
                    info: BinderInfo::Default,
                };
                ctx.push(minor);
                minors.push(minor);
                ctor_fields[owner_index].push(fields);
            }
        }

        let mut declarations = Vec::with_capacity(group.families.len());
        let mut global_minor_index = 0;
        for (owner_index, family) in group.families.iter().enumerate() {
            let rec_name = self.name_str(family.name, "rec");
            let rec_indices = self.open_group_indices(&mut ctx, num_params, &params, family);
            let major_type = self.apply_family(family.ind_const, &params, &rec_indices);
            let major = LocalDecl {
                fvar: ctx.fresh_fvar(),
                name: self.name_str_anon("t"),
                ty: major_type,
                info: BinderInfo::Default,
            };
            let mut result = self.fvar(motives[owner_index].fvar);
            for index in &rec_indices {
                let value = self.fvar(index.fvar);
                result = self.app(result, value);
            }
            let major_value = self.fvar(major.fvar);
            result = self.app(result, major_value);
            let rec_ty = self.abstr_pi_telescope(&[major], result);
            let rec_ty = self.abstr_pi_telescope(&rec_indices, rec_ty);
            let rec_ty = self.abstr_pi_telescope(&minors, rec_ty);
            let rec_ty = self.abstr_pi_telescope(&motives, rec_ty);
            let rec_ty = self.abstr_pi_telescope(&params, rec_ty);

            let mut rules = Vec::with_capacity(family.constructors.len());
            for (constructor_index, constructor) in family.constructors.iter().enumerate() {
                let fields = &ctor_fields[owner_index][constructor_index];
                let mut body = self.fvar(minors[global_minor_index].fvar);
                for field in fields {
                    let value = self.fvar(field.fvar);
                    body = self.app(body, value);
                }
                for &recursive_field in &constructor.recursive_fields {
                    let opened = self.reopen_group_recursive_field(
                        group,
                        &param_values,
                        owner_index,
                        constructor.name,
                        recursive_field,
                        fields,
                        &mut ctx,
                    )?;
                    let target = &group.families[recursive_field.target_family];
                    let target_rec_name = self.name_str(target.name, "rec");
                    let mut recursive_call = self.const_(target_rec_name, rec_level_args.clone());
                    for parameter in &params {
                        let value = self.fvar(parameter.fvar);
                        recursive_call = self.app(recursive_call, value);
                    }
                    for motive in &motives {
                        let value = self.fvar(motive.fvar);
                        recursive_call = self.app(recursive_call, value);
                    }
                    for minor in &minors {
                        let value = self.fvar(minor.fvar);
                        recursive_call = self.app(recursive_call, value);
                    }
                    for index in opened.indices {
                        recursive_call = self.app(recursive_call, index);
                    }
                    let Some(value) = opened.applied_value else {
                        return Err(KernelError::RecursiveFieldShapeMismatch {
                            inductive: family.name,
                            ctor: constructor.name,
                            field_index: u32::try_from(recursive_field.field_index)
                                .unwrap_or(u32::MAX),
                        });
                    };
                    recursive_call = self.app(recursive_call, value);
                    recursive_call = self.abstr_lambda_telescope(&opened.telescope, recursive_call);
                    body = self.app(body, recursive_call);
                }

                let value = self.abstr_lambda_telescope(fields, body);
                let value = self.abstr_lambda_telescope(&minors, value);
                let value = self.abstr_lambda_telescope(&motives, value);
                let value = self.abstr_lambda_telescope(&params, value);
                rules.push(RecRule {
                    ctor_name: constructor.name,
                    num_fields: u16::try_from(fields.len()).expect("field count fits u16"),
                    value,
                });
                global_minor_index += 1;
            }

            let mut check_ctx = LocalContext::new();
            let rec_ty_type = self.infer_core(rec_ty, &mut check_ctx)?;
            let rec_ty_type = self.whnf(rec_ty_type);
            if !matches!(self.expr_node(rec_ty_type), ExprNode::Sort(_)) {
                return Err(KernelError::DeclarationTypeNotASort { got: rec_ty_type });
            }
            declarations.push(Declaration::Recursor {
                name: rec_name,
                uparams: rec_uparams.clone(),
                ty: rec_ty,
                rec_rules: rules,
                num_motives: u16::try_from(motives.len()).expect("motive count fits u16"),
                num_minors: u16::try_from(minors.len()).expect("minor count fits u16"),
                num_params: u16::try_from(num_params).expect("parameter count fits u16"),
                num_indices: u16::try_from(family.num_indices).expect("index count fits u16"),
            });
            for _ in 0..rec_indices.len() {
                ctx.pop();
            }
        }
        Ok(declarations)
    }

    fn open_group_params(
        &mut self,
        ctx: &mut LocalContext,
        num_params: usize,
        family_ty: ExprId,
    ) -> Vec<LocalDecl> {
        let mut params = Vec::with_capacity(num_params);
        let mut cursor = self.whnf(family_ty);
        for _ in 0..num_params {
            let ExprNode::Pi(name, domain, body, info) = self.expr_node(cursor).clone() else {
                break;
            };
            let parameter = LocalDecl {
                fvar: ctx.fresh_fvar(),
                name,
                ty: domain,
                info,
            };
            ctx.push(parameter);
            params.push(parameter);
            let value = self.fvar(parameter.fvar);
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
        }
        params
    }

    fn open_group_indices(
        &mut self,
        ctx: &mut LocalContext,
        num_params: usize,
        params: &[LocalDecl],
        family: &CheckedFamily,
    ) -> Vec<LocalDecl> {
        let mut cursor = self.whnf(family.ty);
        for parameter in params.iter().take(num_params) {
            let ExprNode::Pi(_, _, body, _) = self.expr_node(cursor).clone() else {
                break;
            };
            let value = self.fvar(parameter.fvar);
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
        }
        let mut indices = Vec::with_capacity(family.num_indices);
        for _ in 0..family.num_indices {
            let ExprNode::Pi(name, domain, body, info) = self.expr_node(cursor).clone() else {
                break;
            };
            let index = LocalDecl {
                fvar: ctx.fresh_fvar(),
                name,
                ty: domain,
                info,
            };
            ctx.push(index);
            indices.push(index);
            let value = self.fvar(index.fvar);
            cursor = self.instantiate(body, &[value]);
            cursor = self.whnf(cursor);
        }
        indices
    }

    fn apply_family(
        &mut self,
        family: ExprId,
        params: &[LocalDecl],
        indices: &[LocalDecl],
    ) -> ExprId {
        let mut app = family;
        for local in params.iter().chain(indices) {
            let value = self.fvar(local.fvar);
            app = self.app(app, value);
        }
        app
    }

    #[allow(clippy::too_many_arguments)]
    fn open_group_ih_locals(
        &mut self,
        ctx: &mut LocalContext,
        group: &CheckedInductiveGroup,
        owner_index: usize,
        param_values: &[ExprId],
        constructor: &CheckedCtor,
        motives: &[LocalDecl],
        fields: &[LocalDecl],
    ) -> Result<Vec<LocalDecl>, KernelError> {
        let mut ihs = Vec::with_capacity(constructor.recursive_fields.len());
        for &recursive_field in &constructor.recursive_fields {
            let opened = self.reopen_group_recursive_field(
                group,
                param_values,
                owner_index,
                constructor.name,
                recursive_field,
                fields,
                ctx,
            )?;
            let mut ih_body = self.fvar(motives[recursive_field.target_family].fvar);
            for index in opened.indices {
                ih_body = self.app(ih_body, index);
            }
            let Some(value) = opened.applied_value else {
                return Err(KernelError::RecursiveFieldShapeMismatch {
                    inductive: group.families[owner_index].name,
                    ctor: constructor.name,
                    field_index: u32::try_from(recursive_field.field_index).unwrap_or(u32::MAX),
                });
            };
            ih_body = self.app(ih_body, value);
            let ih_ty = self.abstr_pi_telescope(&opened.telescope, ih_body);
            let ih = LocalDecl {
                fvar: ctx.fresh_fvar(),
                name: self.name_str_anon("ih"),
                ty: ih_ty,
                info: BinderInfo::Default,
            };
            ctx.push(ih);
            ihs.push(ih);
        }
        Ok(ihs)
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
