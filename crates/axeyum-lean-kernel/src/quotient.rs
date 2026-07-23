//! Lean 4.30's privileged fixed quotient package (ADR-0365, TL2.10).
//!
//! Quotients are neither axioms nor an ordinary inductive encoding. The kernel
//! validates canonical `Eq`/`Eq.refl`, independently derives the four package
//! types, and admits all four declarations transactionally. Dedicated
//! `Quot.lift`/`Quot.ind` reduction is implemented in the type checker after
//! package admission; the package constructor and its failure atomicity live
//! here.

use std::collections::{BTreeSet, HashSet};

use crate::env::{Declaration, QuotKind};
use crate::expr::{BinderInfo, ExprId, ExprNode};
use crate::name::NameId;
use crate::{Kernel, KernelError};

const PACKAGE_LEN: usize = 4;
const LOCAL_BASE: u64 = u64::MAX - 32;

#[derive(Clone, Copy)]
struct QuotientNames {
    eq: NameId,
    eq_refl: NameId,
    quot: NameId,
    quot_mk: NameId,
    quot_lift: NameId,
    quot_ind: NameId,
}

#[derive(Clone, Copy)]
struct PiBinder {
    name: NameId,
    fvar: u64,
    ty: ExprId,
    info: BinderInfo,
}

impl Kernel {
    /// Validate and atomically admit Lean's exact four-declaration quotient
    /// package.
    ///
    /// The supplied declarations are untrusted candidates. Their exact names,
    /// order, kinds, universe arities, binder information, and types are checked
    /// against independently synthesized Lean 4.30 contracts after canonical
    /// `Eq`/`Eq.refl` validation. Binder display names and universe-parameter
    /// display names are non-semantic; parameter positions remain exact.
    ///
    /// Reapplying the same valid package to an already canonical environment is
    /// idempotent. Any partial or conflicting reserved-name population rejects.
    /// Ordinary [`Kernel::add_declaration`] rejects every individual
    /// [`Declaration::Quotient`].
    ///
    /// # Errors
    ///
    /// Returns a typed quotient-package error for malformed input or bootstrap
    /// state, [`KernelError::DeclarationTypeNotASort`] (or another ordinary
    /// checker error) if a validated candidate fails type checking, and leaves
    /// the declaration environment unchanged on every error.
    pub fn add_quotient_package(
        &mut self,
        declarations: &[Declaration],
    ) -> Result<(), KernelError> {
        let names = self.quotient_names();
        self.validate_quotient_eq(names)?;
        self.validate_quotient_package(names, declarations)?;

        let reserved = [names.quot, names.quot_mk, names.quot_lift, names.quot_ind];
        let present = reserved.map(|name| self.env.contains(name));
        if present.iter().all(|present| *present) {
            let mut existing = Vec::with_capacity(PACKAGE_LEN);
            for name in reserved {
                let Some(declaration) = self.env.get(name).cloned() else {
                    return Err(KernelError::QuotientPackageConflict { name });
                };
                existing.push(declaration);
            }
            self.validate_quotient_package(names, &existing)?;
            return Ok(());
        }
        if let Some((index, _)) = present.iter().enumerate().find(|(_, present)| **present) {
            return Err(KernelError::QuotientPackageConflict {
                name: reserved[index],
            });
        }

        self.with_quotient_transaction(|kernel| {
            for declaration in declarations {
                kernel.check_declaration(declaration)?;
                kernel.env.insert_unchecked(declaration.clone());
            }
            Ok(())
        })
    }

    fn with_quotient_transaction<T>(
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

    fn quotient_names(&mut self) -> QuotientNames {
        let root = self.anon();
        let eq = self.name_str(root, "Eq");
        let quot = self.name_str(root, "Quot");
        QuotientNames {
            eq,
            eq_refl: self.name_str(eq, "refl"),
            quot,
            quot_mk: self.name_str(quot, "mk"),
            quot_lift: self.name_str(quot, "lift"),
            quot_ind: self.name_str(quot, "ind"),
        }
    }

    fn validate_quotient_eq(&mut self, names: QuotientNames) -> Result<(), KernelError> {
        let Some(eq_declaration) = self.env.get(names.eq).cloned() else {
            return Err(KernelError::QuotientEqBootstrapMismatch { name: names.eq });
        };
        let Declaration::Inductive {
            uparams,
            ty,
            num_params,
            num_indices,
            is_recursive,
            ctor_names,
            ..
        } = eq_declaration
        else {
            return Err(KernelError::QuotientEqBootstrapMismatch { name: names.eq });
        };
        if uparams.len() != 1
            || num_params != 2
            || num_indices != 1
            || is_recursive
            || ctor_names.as_slice() != [names.eq_refl]
        {
            return Err(KernelError::QuotientEqBootstrapMismatch { name: names.eq });
        }
        let expected_eq = self.expected_eq_type(uparams[0]);
        if !self.quotient_type_matches(ty, expected_eq) {
            return Err(KernelError::QuotientEqBootstrapMismatch { name: names.eq });
        }

        let Some(refl_declaration) = self.env.get(names.eq_refl).cloned() else {
            return Err(KernelError::QuotientEqBootstrapMismatch {
                name: names.eq_refl,
            });
        };
        let Declaration::Constructor {
            uparams,
            ty,
            inductive,
            idx,
            num_fields,
            ..
        } = refl_declaration
        else {
            return Err(KernelError::QuotientEqBootstrapMismatch {
                name: names.eq_refl,
            });
        };
        if uparams.len() != 1 || inductive != names.eq || idx != 0 || num_fields != 0 {
            return Err(KernelError::QuotientEqBootstrapMismatch {
                name: names.eq_refl,
            });
        }
        let expected_refl = self.expected_eq_refl_type(names.eq, uparams[0]);
        if !self.quotient_type_matches(ty, expected_refl) {
            return Err(KernelError::QuotientEqBootstrapMismatch {
                name: names.eq_refl,
            });
        }
        Ok(())
    }

    fn validate_quotient_package(
        &mut self,
        names: QuotientNames,
        declarations: &[Declaration],
    ) -> Result<(), KernelError> {
        if declarations.len() != PACKAGE_LEN {
            return Err(KernelError::QuotientPackageLength {
                expected: PACKAGE_LEN,
                got: declarations.len(),
            });
        }
        let expected_names = [names.quot, names.quot_mk, names.quot_lift, names.quot_ind];
        let expected_kinds = [
            QuotKind::Type,
            QuotKind::Ctor,
            QuotKind::Lift,
            QuotKind::Ind,
        ];
        let expected_arities = [1, 1, 2, 1];

        for (index, declaration) in declarations.iter().enumerate() {
            if declaration.name() != expected_names[index] {
                return Err(KernelError::QuotientPackageNameMismatch {
                    index,
                    expected: expected_names[index],
                    got: declaration.name(),
                });
            }
            let Declaration::Quotient {
                name,
                uparams,
                ty,
                kind,
            } = declaration
            else {
                return Err(KernelError::QuotientPackageRequired {
                    name: declaration.name(),
                });
            };
            if *kind != expected_kinds[index] {
                return Err(KernelError::QuotientPackageKindMismatch {
                    name: *name,
                    expected: expected_kinds[index],
                    got: *kind,
                });
            }
            let distinct = uparams.iter().copied().collect::<BTreeSet<_>>().len();
            if uparams.len() != expected_arities[index] || distinct != expected_arities[index] {
                return Err(KernelError::QuotientUniverseParametersMismatch {
                    name: *name,
                    expected: expected_arities[index],
                    got: uparams.len(),
                });
            }
            let expected_type = self.expected_quotient_type(names, *kind, uparams);
            if !self.quotient_type_matches(*ty, expected_type) {
                return Err(KernelError::QuotientTypeMismatch { name: *name });
            }
        }
        Ok(())
    }

    fn expected_eq_type(&mut self, uparam: NameId) -> ExprId {
        let names = self.quotient_binder_names();
        let alpha = self.fvar(LOCAL_BASE);
        let sort_u = self.sort_for_param(uparam);
        let prop = self.sort_zero();
        let relation_tail = self.arrow(alpha, prop);
        let relation = self.arrow(alpha, relation_tail);
        self.close_pi(
            &[PiBinder {
                name: names.alpha,
                fvar: LOCAL_BASE,
                ty: sort_u,
                info: BinderInfo::Implicit,
            }],
            relation,
        )
    }

    fn expected_eq_refl_type(&mut self, eq: NameId, uparam: NameId) -> ExprId {
        let names = self.quotient_binder_names();
        let alpha_id = LOCAL_BASE;
        let a_id = LOCAL_BASE + 1;
        let alpha = self.fvar(alpha_id);
        let a = self.fvar(a_id);
        let level = self.level_param(uparam);
        let eq_const = self.const_(eq, vec![level]);
        let result = self.apps(eq_const, &[alpha, a, a]);
        let sort_u = self.sort(level);
        self.close_pi(
            &[
                PiBinder {
                    name: names.alpha,
                    fvar: alpha_id,
                    ty: sort_u,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: names.a,
                    fvar: a_id,
                    ty: alpha,
                    info: BinderInfo::Default,
                },
            ],
            result,
        )
    }

    fn expected_quotient_type(
        &mut self,
        names: QuotientNames,
        kind: QuotKind,
        uparams: &[NameId],
    ) -> ExprId {
        match kind {
            QuotKind::Type => self.expected_quot_type(uparams[0]),
            QuotKind::Ctor => self.expected_quot_mk_type(names, uparams[0]),
            QuotKind::Lift => self.expected_quot_lift_type(names, uparams[0], uparams[1]),
            QuotKind::Ind => self.expected_quot_ind_type(names, uparams[0]),
        }
    }

    fn expected_quot_type(&mut self, uparam: NameId) -> ExprId {
        let names = self.quotient_binder_names();
        let alpha_id = LOCAL_BASE;
        let r_id = LOCAL_BASE + 1;
        let alpha = self.fvar(alpha_id);
        let relation = self.relation_type(alpha);
        let sort_u = self.sort_for_param(uparam);
        self.close_pi(
            &[
                PiBinder {
                    name: names.alpha,
                    fvar: alpha_id,
                    ty: sort_u,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: names.r,
                    fvar: r_id,
                    ty: relation,
                    info: BinderInfo::Default,
                },
            ],
            sort_u,
        )
    }

    fn expected_quot_mk_type(&mut self, names: QuotientNames, uparam: NameId) -> ExprId {
        let binder_names = self.quotient_binder_names();
        let alpha_id = LOCAL_BASE;
        let r_id = LOCAL_BASE + 1;
        let a_id = LOCAL_BASE + 2;
        let alpha = self.fvar(alpha_id);
        let relation = self.relation_type(alpha);
        let r = self.fvar(r_id);
        let level = self.level_param(uparam);
        let quot = self.const_(names.quot, vec![level]);
        let result = self.apps(quot, &[alpha, r]);
        let sort_u = self.sort(level);
        self.close_pi(
            &[
                PiBinder {
                    name: binder_names.alpha,
                    fvar: alpha_id,
                    ty: sort_u,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: binder_names.r,
                    fvar: r_id,
                    ty: relation,
                    info: BinderInfo::Default,
                },
                PiBinder {
                    name: binder_names.a,
                    fvar: a_id,
                    ty: alpha,
                    info: BinderInfo::Default,
                },
            ],
            result,
        )
    }

    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn expected_quot_lift_type(
        &mut self,
        names: QuotientNames,
        source_level_param: NameId,
        target_level_param: NameId,
    ) -> ExprId {
        let binder_names = self.quotient_binder_names();
        let alpha_id = LOCAL_BASE;
        let r_id = LOCAL_BASE + 1;
        let beta_id = LOCAL_BASE + 2;
        let f_id = LOCAL_BASE + 3;
        let sanity_id = LOCAL_BASE + 4;
        let q_id = LOCAL_BASE + 5;
        let a_id = LOCAL_BASE + 6;
        let b_id = LOCAL_BASE + 7;

        let alpha = self.fvar(alpha_id);
        let r = self.fvar(r_id);
        let beta = self.fvar(beta_id);
        let f = self.fvar(f_id);
        let a = self.fvar(a_id);
        let b = self.fvar(b_id);
        let u = self.level_param(source_level_param);
        let v = self.level_param(target_level_param);
        let quot_const = self.const_(names.quot, vec![u]);
        let quot = self.apps(quot_const, &[alpha, r]);
        let r_ab = self.apps(r, &[a, b]);
        let f_a = self.app(f, a);
        let f_b = self.app(f, b);
        let eq_const = self.const_(names.eq, vec![v]);
        let equality = self.apps(eq_const, &[beta, f_a, f_b]);
        let proof = self.arrow(r_ab, equality);
        let sanity = self.close_pi(
            &[
                PiBinder {
                    name: binder_names.a,
                    fvar: a_id,
                    ty: alpha,
                    info: BinderInfo::Default,
                },
                PiBinder {
                    name: binder_names.b,
                    fvar: b_id,
                    ty: alpha,
                    info: BinderInfo::Default,
                },
            ],
            proof,
        );
        let sort_u = self.sort(u);
        let sort_v = self.sort(v);
        let function = self.arrow(alpha, beta);
        let relation = self.relation_type(alpha);
        self.close_pi(
            &[
                PiBinder {
                    name: binder_names.alpha,
                    fvar: alpha_id,
                    ty: sort_u,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: binder_names.r,
                    fvar: r_id,
                    ty: relation,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: binder_names.beta,
                    fvar: beta_id,
                    ty: sort_v,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: binder_names.f,
                    fvar: f_id,
                    ty: function,
                    info: BinderInfo::Default,
                },
                PiBinder {
                    name: binder_names.sanity,
                    fvar: sanity_id,
                    ty: sanity,
                    info: BinderInfo::Default,
                },
                PiBinder {
                    name: binder_names.q,
                    fvar: q_id,
                    ty: quot,
                    info: BinderInfo::Default,
                },
            ],
            beta,
        )
    }

    #[allow(clippy::too_many_lines)]
    fn expected_quot_ind_type(&mut self, names: QuotientNames, uparam: NameId) -> ExprId {
        let binder_names = self.quotient_binder_names();
        let alpha_id = LOCAL_BASE;
        let r_id = LOCAL_BASE + 1;
        let beta_id = LOCAL_BASE + 2;
        let minor_id = LOCAL_BASE + 3;
        let q_id = LOCAL_BASE + 4;
        let a_id = LOCAL_BASE + 5;

        let alpha = self.fvar(alpha_id);
        let r = self.fvar(r_id);
        let beta = self.fvar(beta_id);
        let q = self.fvar(q_id);
        let a = self.fvar(a_id);
        let u = self.level_param(uparam);
        let quot_const = self.const_(names.quot, vec![u]);
        let quot = self.apps(quot_const, &[alpha, r]);
        let mk_const = self.const_(names.quot_mk, vec![u]);
        let mk_a = self.apps(mk_const, &[alpha, r, a]);
        let beta_mk_a = self.app(beta, mk_a);
        let minor = self.close_pi(
            &[PiBinder {
                name: binder_names.a,
                fvar: a_id,
                ty: alpha,
                info: BinderInfo::Default,
            }],
            beta_mk_a,
        );
        let prop = self.sort_zero();
        let predicate = self.arrow(quot, prop);
        let sort_u = self.sort(u);
        let result = self.app(beta, q);
        let relation = self.relation_type(alpha);
        self.close_pi(
            &[
                PiBinder {
                    name: binder_names.alpha,
                    fvar: alpha_id,
                    ty: sort_u,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: binder_names.r,
                    fvar: r_id,
                    ty: relation,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: binder_names.beta,
                    fvar: beta_id,
                    ty: predicate,
                    info: BinderInfo::Implicit,
                },
                PiBinder {
                    name: binder_names.sanity,
                    fvar: minor_id,
                    ty: minor,
                    info: BinderInfo::Default,
                },
                PiBinder {
                    name: binder_names.q,
                    fvar: q_id,
                    ty: quot,
                    info: BinderInfo::Default,
                },
            ],
            result,
        )
    }

    fn quotient_binder_names(&mut self) -> QuotientBinderNames {
        let root = self.anon();
        QuotientBinderNames {
            alpha: self.name_str(root, "α"),
            r: self.name_str(root, "r"),
            beta: self.name_str(root, "β"),
            f: self.name_str(root, "f"),
            a: self.name_str(root, "a"),
            b: self.name_str(root, "b"),
            sanity: self.name_str(root, "h"),
            q: self.name_str(root, "q"),
        }
    }

    fn sort_for_param(&mut self, parameter: NameId) -> ExprId {
        let level = self.level_param(parameter);
        self.sort(level)
    }

    fn relation_type(&mut self, alpha: ExprId) -> ExprId {
        let prop = self.sort_zero();
        let inner = self.arrow(alpha, prop);
        self.arrow(alpha, inner)
    }

    fn arrow(&mut self, domain: ExprId, codomain: ExprId) -> ExprId {
        let anonymous = self.anon();
        self.pi(anonymous, domain, codomain, BinderInfo::Default)
    }

    fn apps(&mut self, head: ExprId, arguments: &[ExprId]) -> ExprId {
        arguments
            .iter()
            .copied()
            .fold(head, |function, argument| self.app(function, argument))
    }

    fn close_pi(&mut self, binders: &[PiBinder], mut body: ExprId) -> ExprId {
        for binder in binders.iter().rev() {
            body = self.abstract_fvars(body, &[binder.fvar]);
            body = self.pi(binder.name, binder.ty, body, binder.info);
        }
        body
    }

    /// Exact package-type comparison modulo binder display names. Binder info,
    /// de Bruijn structure, constant names, levels, and every other node remain
    /// structural.
    fn quotient_type_matches(&self, left: ExprId, right: ExprId) -> bool {
        fn go(
            kernel: &Kernel,
            left: ExprId,
            right: ExprId,
            seen: &mut HashSet<(ExprId, ExprId)>,
        ) -> bool {
            if left == right || !seen.insert((left, right)) {
                return true;
            }
            match (kernel.expr_node(left), kernel.expr_node(right)) {
                (ExprNode::BVar(a), ExprNode::BVar(b)) => a == b,
                (ExprNode::FVar(a), ExprNode::FVar(b)) => a == b,
                (ExprNode::Sort(a), ExprNode::Sort(b)) => a == b,
                (ExprNode::Const(an, al), ExprNode::Const(bn, bl)) => an == bn && al == bl,
                (ExprNode::Proj(an, ai, av), ExprNode::Proj(bn, bi, bv)) => {
                    an == bn && ai == bi && go(kernel, *av, *bv, seen)
                }
                (ExprNode::App(af, aa), ExprNode::App(bf, ba)) => {
                    go(kernel, *af, *bf, seen) && go(kernel, *aa, *ba, seen)
                }
                (ExprNode::Lam(_, at, ab, ai), ExprNode::Lam(_, bt, bb, bi))
                | (ExprNode::Pi(_, at, ab, ai), ExprNode::Pi(_, bt, bb, bi)) => {
                    ai == bi && go(kernel, *at, *bt, seen) && go(kernel, *ab, *bb, seen)
                }
                (ExprNode::Let(_, at, av, ab), ExprNode::Let(_, bt, bv, bb)) => {
                    go(kernel, *at, *bt, seen)
                        && go(kernel, *av, *bv, seen)
                        && go(kernel, *ab, *bb, seen)
                }
                (ExprNode::Lit(a), ExprNode::Lit(b)) => a == b,
                _ => false,
            }
        }

        go(self, left, right, &mut HashSet::new())
    }

    #[cfg(test)]
    fn canonical_quotient_package(
        &mut self,
        source_level_param: NameId,
        target_level_param: NameId,
    ) -> Vec<Declaration> {
        let names = self.quotient_names();
        [
            (names.quot, QuotKind::Type, vec![source_level_param]),
            (names.quot_mk, QuotKind::Ctor, vec![source_level_param]),
            (
                names.quot_lift,
                QuotKind::Lift,
                vec![source_level_param, target_level_param],
            ),
            (names.quot_ind, QuotKind::Ind, vec![source_level_param]),
        ]
        .into_iter()
        .map(|(name, kind, uparams)| Declaration::Quotient {
            name,
            ty: self.expected_quotient_type(names, kind, &uparams),
            uparams,
            kind,
        })
        .collect()
    }
}

#[derive(Clone, Copy)]
struct QuotientBinderNames {
    alpha: NameId,
    r: NameId,
    beta: NameId,
    f: NameId,
    a: NameId,
    b: NameId,
    sanity: NameId,
    q: NameId,
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    fn declare_canonical_eq(kernel: &mut Kernel) {
        let names = kernel.quotient_names();
        let root = kernel.anon();
        let uparam = kernel.name_str(root, "eq_u");
        let eq_ty = kernel.expected_eq_type(uparam);
        let refl_ty = kernel.expected_eq_refl_type(names.eq, uparam);
        kernel
            .add_inductive(names.eq, &[uparam], 2, eq_ty, &[(names.eq_refl, refl_ty)])
            .expect("canonical Eq should admit");
    }

    fn package(kernel: &mut Kernel) -> Vec<Declaration> {
        let root = kernel.anon();
        let u = kernel.name_str(root, "quot_u");
        let v = kernel.name_str(root, "quot_v");
        kernel.canonical_quotient_package(u, v)
    }

    fn rename_binders(
        kernel: &mut Kernel,
        expression: ExprId,
        name: NameId,
        memo: &mut HashMap<ExprId, ExprId>,
    ) -> ExprId {
        if let Some(renamed) = memo.get(&expression) {
            return *renamed;
        }
        let renamed = match kernel.expr_node(expression).clone() {
            ExprNode::Proj(type_name, field, structure) => {
                let structure = rename_binders(kernel, structure, name, memo);
                kernel.proj(type_name, field, structure)
            }
            ExprNode::App(function, argument) => {
                let function = rename_binders(kernel, function, name, memo);
                let argument = rename_binders(kernel, argument, name, memo);
                kernel.app(function, argument)
            }
            ExprNode::Lam(_, ty, body, info) => {
                let ty = rename_binders(kernel, ty, name, memo);
                let body = rename_binders(kernel, body, name, memo);
                kernel.lam(name, ty, body, info)
            }
            ExprNode::Pi(_, ty, body, info) => {
                let ty = rename_binders(kernel, ty, name, memo);
                let body = rename_binders(kernel, body, name, memo);
                kernel.pi(name, ty, body, info)
            }
            ExprNode::Let(_, ty, value, body) => {
                let ty = rename_binders(kernel, ty, name, memo);
                let value = rename_binders(kernel, value, name, memo);
                let body = rename_binders(kernel, body, name, memo);
                kernel.let_(name, ty, value, body)
            }
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Const(_, _)
            | ExprNode::Lit(_) => expression,
        };
        memo.insert(expression, renamed);
        renamed
    }

    #[test]
    fn canonical_package_admits_exactly_four_and_is_idempotent() {
        let mut kernel = Kernel::new();
        declare_canonical_eq(&mut kernel);
        let before = kernel.environment().len();
        let declarations = package(&mut kernel);
        kernel
            .add_quotient_package(&declarations)
            .expect("canonical quotient package should admit");
        assert_eq!(kernel.environment().len(), before + PACKAGE_LEN);
        for declaration in &declarations {
            assert_eq!(
                kernel.environment().get(declaration.name()),
                Some(declaration)
            );
        }
        kernel
            .add_quotient_package(&declarations)
            .expect("canonical quotient initialization should be idempotent");
        assert_eq!(kernel.environment().len(), before + PACKAGE_LEN);
    }

    #[test]
    fn direct_quotient_declaration_requires_package_gate() {
        let mut kernel = Kernel::new();
        declare_canonical_eq(&mut kernel);
        let declaration = package(&mut kernel).remove(0);
        let name = declaration.name();
        assert_eq!(
            kernel.add_declaration(declaration),
            Err(KernelError::QuotientPackageRequired { name })
        );
        assert!(!kernel.environment().contains(name));
    }

    #[test]
    fn missing_or_noninductive_eq_rejects_without_publication() {
        let mut kernel = Kernel::new();
        let declarations = package(&mut kernel);
        let eq = kernel.quotient_names().eq;
        assert_eq!(
            kernel.add_quotient_package(&declarations),
            Err(KernelError::QuotientEqBootstrapMismatch { name: eq })
        );

        let prop = kernel.sort_zero();
        kernel
            .add_declaration(Declaration::Axiom {
                name: eq,
                uparams: vec![],
                ty: prop,
            })
            .expect("malformed Eq control is still an ordinary axiom");
        assert_eq!(
            kernel.add_quotient_package(&declarations),
            Err(KernelError::QuotientEqBootstrapMismatch { name: eq })
        );
        assert!(
            declarations
                .iter()
                .all(|declaration| !kernel.environment().contains(declaration.name()))
        );
    }

    #[test]
    fn order_kind_universe_and_type_mutations_reject() {
        let mut kernel = Kernel::new();
        declare_canonical_eq(&mut kernel);
        let baseline = kernel.environment().len();

        let mut reordered = package(&mut kernel);
        reordered.swap(0, 1);
        assert!(matches!(
            kernel.add_quotient_package(&reordered),
            Err(KernelError::QuotientPackageNameMismatch { index: 0, .. })
        ));

        let mut wrong_kind = package(&mut kernel);
        let Declaration::Quotient { kind, .. } = &mut wrong_kind[1] else {
            unreachable!()
        };
        *kind = QuotKind::Ind;
        assert!(matches!(
            kernel.add_quotient_package(&wrong_kind),
            Err(KernelError::QuotientPackageKindMismatch { .. })
        ));

        let mut aliased_universes = package(&mut kernel);
        let Declaration::Quotient { uparams, .. } = &mut aliased_universes[2] else {
            unreachable!()
        };
        uparams[1] = uparams[0];
        assert!(matches!(
            kernel.add_quotient_package(&aliased_universes),
            Err(KernelError::QuotientUniverseParametersMismatch { .. })
        ));

        let mut wrong_type = package(&mut kernel);
        let prop = kernel.sort_zero();
        let Declaration::Quotient { ty, .. } = &mut wrong_type[3] else {
            unreachable!()
        };
        *ty = prop;
        assert!(matches!(
            kernel.add_quotient_package(&wrong_type),
            Err(KernelError::QuotientTypeMismatch { .. })
        ));
        assert_eq!(kernel.environment().len(), baseline);
    }

    #[test]
    fn binder_display_names_are_nonsemantic_but_binder_info_is_exact() {
        let mut kernel = Kernel::new();
        declare_canonical_eq(&mut kernel);
        let mut declarations = package(&mut kernel);
        let root = kernel.anon();
        let renamed = kernel.name_str(root, "renamed");
        for declaration in &mut declarations {
            let Declaration::Quotient { ty, .. } = declaration else {
                unreachable!()
            };
            *ty = rename_binders(&mut kernel, *ty, renamed, &mut HashMap::new());
        }
        kernel
            .add_quotient_package(&declarations)
            .expect("binder display names must not affect package shape");

        let mut wrong_info = package(&mut kernel);
        let Declaration::Quotient { ty, .. } = &mut wrong_info[0] else {
            unreachable!()
        };
        let ExprNode::Pi(name, domain, body, _) = kernel.expr_node(*ty).clone() else {
            unreachable!()
        };
        *ty = kernel.pi(name, domain, body, BinderInfo::Default);
        assert!(matches!(
            kernel.add_quotient_package(&wrong_info),
            Err(KernelError::QuotientTypeMismatch { .. })
        ));
    }

    #[test]
    fn partial_reserved_population_and_transaction_failure_leave_no_suffix() {
        let mut kernel = Kernel::new();
        declare_canonical_eq(&mut kernel);
        let declarations = package(&mut kernel);
        let first = declarations[0].clone();
        let first_name = first.name();
        kernel.env.insert_unchecked(first);
        assert_eq!(
            kernel.add_quotient_package(&declarations),
            Err(KernelError::QuotientPackageConflict { name: first_name })
        );
        assert!(kernel.environment().contains(first_name));
        assert!(
            declarations[1..]
                .iter()
                .all(|declaration| !kernel.environment().contains(declaration.name()))
        );

        let mut fresh = Kernel::new();
        let declarations = package(&mut fresh);
        let inserted = declarations[0].clone();
        let inserted_name = inserted.name();
        let failure = fresh.with_quotient_transaction(|kernel| {
            kernel.env.insert_unchecked(inserted);
            Err::<(), _>(KernelError::QuotientTypeMismatch {
                name: inserted_name,
            })
        });
        assert!(matches!(
            failure,
            Err(KernelError::QuotientTypeMismatch { .. })
        ));
        assert!(!fresh.environment().contains(inserted_name));
    }
}
