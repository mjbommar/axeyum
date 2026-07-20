//! Direct structural certificate validation and Lean reconstruction.

use super::{
    BinderInfo, BTreeMap, BTreeSet, Declaration, ExprId, FINITE_DOMAIN_ENUM_CERT_BITS, FuncId, IrOp,
    IrSort, IrTermNode, ProofFragment, ReconstructCtx, ReconstructError, TermArena, TermId,
    and_chain_prop_of, and_intro_fold, fresh_axiom, reflexive_disequality_assertion,
    render_ctx_module, require_infers_false,
};

#[derive(Debug, Clone, Copy)]
struct FiniteDomainPigeonholeLeanInstance {
    function: FuncId,
    args: [TermId; 3],
}

pub(super) fn finite_domain_pigeonhole_certifies(
    arena: &TermArena,
    assertions: &[TermId],
) -> bool {
    finite_domain_pigeonhole_lean_instance(arena, assertions).is_some()
}

fn finite_domain_pigeonhole_lean_instance(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<FiniteDomainPigeonholeLeanInstance> {
    let cert = crate::ufbv_finite::finite_domain_pigeonhole_refutation(arena, assertions)?;
    if cert.domain_size != 2 || cert.applications.len() < 3 {
        return None;
    }
    let (_, params, _) = arena.function(cert.function);
    let [param] = params else {
        return None;
    };
    if !matches!(param, IrSort::Bool | IrSort::BitVec(1)) {
        return None;
    }

    let applications = [
        cert.applications[0],
        cert.applications[1],
        cert.applications[2],
    ];
    let mut args = Vec::with_capacity(3);
    for app in applications {
        let (func, app_args) = finite_domain_direct_application(arena, app)?;
        if func != cert.function {
            return None;
        }
        let [arg] = app_args else {
            return None;
        };
        if !matches!(arena.sort_of(*arg), IrSort::Bool | IrSort::BitVec(1)) {
            return None;
        }
        args.push(*arg);
    }
    let args = [args[0], args[1], args[2]];

    // This first Lean slice keeps the hypothesis path direct: the three input
    // disequalities must occur with the same ordered pairs the sorted certificate
    // will feed to the proof. Reversed disequalities are evidence-certified but
    // left for the later negation-symmetry reconstruction.
    if !finite_domain_has_ordered_diseqs(arena, assertions, applications) {
        return None;
    }

    Some(FiniteDomainPigeonholeLeanInstance {
        function: cert.function,
        args,
    })
}

fn finite_domain_direct_application(
    arena: &TermArena,
    term: TermId,
) -> Option<(FuncId, &[TermId])> {
    let IrTermNode::App {
        op: IrOp::Apply(func),
        args,
    } = arena.node(term)
    else {
        return None;
    };
    Some((*func, args))
}

fn finite_domain_has_ordered_diseqs(
    arena: &TermArena,
    assertions: &[TermId],
    applications: [TermId; 3],
) -> bool {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_finite_domain_conjuncts(arena, assertion, &mut conjuncts);
    }
    let mut diseqs = BTreeSet::new();
    for conjunct in conjuncts {
        if let Some(pair) = finite_domain_match_diseq(arena, conjunct) {
            diseqs.insert(pair);
        }
    }
    diseqs.contains(&(applications[0], applications[1]))
        && diseqs.contains(&(applications[0], applications[2]))
        && diseqs.contains(&(applications[1], applications[2]))
}

fn collect_finite_domain_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        IrTermNode::App {
            op: IrOp::BoolAnd,
            args,
        } if args.len() == 2 => {
            collect_finite_domain_conjuncts(arena, args[0], out);
            collect_finite_domain_conjuncts(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn finite_domain_match_diseq(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let IrTermNode::App {
        op: IrOp::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let IrTermNode::App { op: IrOp::Eq, args } = arena.node(*inner) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn reconstruct_finite_domain_pigeonhole_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let inst = finite_domain_pigeonhole_lean_instance(arena, assertions).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "finite_domain_pigeonhole".to_owned(),
            detail: "expected three ordered disequalities over one Bool/BV1 function domain"
                .to_owned(),
        }
    })?;

    let mut ctx = ReconstructCtx::new();
    let f = declare_bool_to_alpha_function(&mut ctx, inst.function)?;
    let mut bool_terms = BTreeMap::new();
    let args = [
        finite_domain_arg_expr(&mut ctx, arena, inst.args[0], &mut bool_terms)?,
        finite_domain_arg_expr(&mut ctx, arena, inst.args[1], &mut bool_terms)?,
        finite_domain_arg_expr(&mut ctx, arena, inst.args[2], &mut bool_terms)?,
    ];
    let app = [
        ctx.kernel.app(f, args[0]),
        ctx.kernel.app(f, args[1]),
        ctx.kernel.app(f, args[2]),
    ];
    let h01_prop = finite_domain_ne(&mut ctx, app[0], app[1]);
    let h01 = fresh_axiom(&mut ctx, h01_prop, "assume")?;
    let h02_prop = finite_domain_ne(&mut ctx, app[0], app[2]);
    let h02 = fresh_axiom(&mut ctx, h02_prop, "assume")?;
    let h12_prop = finite_domain_ne(&mut ctx, app[1], app[2]);
    let h12 = fresh_axiom(&mut ctx, h12_prop, "assume")?;

    let proof_fn = build_bool_pigeonhole3(&mut ctx, f);
    let proof = {
        let e = ctx.kernel.app(proof_fn, args[0]);
        let e = ctx.kernel.app(e, args[1]);
        let e = ctx.kernel.app(e, args[2]);
        let e = ctx.kernel.app(e, h01);
        let e = ctx.kernel.app(e, h02);
        ctx.kernel.app(e, h12)
    };
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

fn declare_bool_to_alpha_function(
    ctx: &mut ReconstructCtx,
    function: FuncId,
) -> Result<ExprId, ReconstructError> {
    let name = ctx.fresh_name(&format!("fd_fun_{}", function.index()));
    let bool_ty = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    let ty = {
        let anon = ctx.kernel.anon();
        ctx.kernel.pi(anon, bool_ty, ctx.alpha, BinderInfo::Default)
    };
    ctx.kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "finite_domain_pigeonhole".to_owned(),
            detail: format!("function axiom did not admit: {e:?}"),
        })?;
    Ok(ctx.kernel.const_(name, vec![]))
}

fn finite_domain_arg_expr(
    ctx: &mut ReconstructCtx,
    arena: &TermArena,
    term: TermId,
    bool_terms: &mut BTreeMap<TermId, ExprId>,
) -> Result<ExprId, ReconstructError> {
    match arena.node(term) {
        IrTermNode::BoolConst(value) => return Ok(finite_domain_bool_value(ctx, *value)),
        IrTermNode::BvConst { width: 1, value } => {
            return Ok(finite_domain_bool_value(ctx, (*value & 1) != 0));
        }
        _ => {}
    }
    if let Some(&expr) = bool_terms.get(&term) {
        return Ok(expr);
    }
    let name = ctx.fresh_name(&format!("fd_arg_{}", term.index()));
    let bool_ty = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    ctx.kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty: bool_ty,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "finite_domain_pigeonhole".to_owned(),
            detail: format!("domain-value axiom did not admit: {e:?}"),
        })?;
    let expr = ctx.kernel.const_(name, vec![]);
    bool_terms.insert(term, expr);
    Ok(expr)
}

fn finite_domain_bool_value(ctx: &mut ReconstructCtx, value: bool) -> ExprId {
    let name = if value {
        ctx.prelude.bool_true
    } else {
        ctx.prelude.bool_false
    };
    ctx.kernel.const_(name, vec![])
}

fn finite_domain_ne(ctx: &mut ReconstructCtx, lhs: ExprId, rhs: ExprId) -> ExprId {
    let eq = ctx.mk_eq(lhs, rhs);
    ctx.mk_not(eq)
}

fn finite_domain_bool_ty(ctx: &mut ReconstructCtx) -> ExprId {
    ctx.kernel.const_(ctx.prelude.bool_, vec![])
}

fn finite_domain_false(ctx: &mut ReconstructCtx) -> ExprId {
    ctx.kernel.const_(ctx.prelude.false_, vec![])
}

fn finite_domain_bool_rec(
    ctx: &mut ReconstructCtx,
    motive: ExprId,
    true_case: ExprId,
    false_case: ExprId,
) -> ExprId {
    let zero = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.bool_rec, vec![zero]);
    let e = ctx.kernel.app(rec, motive);
    let e = ctx.kernel.app(e, true_case);
    ctx.kernel.app(e, false_case)
}

fn finite_domain_refl_f(ctx: &mut ReconstructCtx, f: ExprId, value: bool) -> ExprId {
    let arg = finite_domain_bool_value(ctx, value);
    let app = ctx.kernel.app(f, arg);
    ctx.mk_eq_refl(app)
}

fn finite_domain_ne_f(ctx: &mut ReconstructCtx, f: ExprId, lhs: ExprId, rhs: ExprId) -> ExprId {
    let lhs_app = ctx.kernel.app(f, lhs);
    let rhs_app = ctx.kernel.app(f, rhs);
    finite_domain_ne(ctx, lhs_app, rhs_app)
}

fn finite_domain_leaf(ctx: &mut ReconstructCtx, f: ExprId, a: bool, b: bool, c: bool) -> ExprId {
    let (hyp_index, value) = if a == b {
        (2, a)
    } else if a == c {
        (1, a)
    } else {
        (0, b)
    };
    let proof = {
        let h = ctx.kernel.bvar(hyp_index);
        let refl = finite_domain_refl_f(ctx, f, value);
        ctx.kernel.app(h, refl)
    };
    let anon = ctx.kernel.anon();
    let a_expr = finite_domain_bool_value(ctx, a);
    let b_expr = finite_domain_bool_value(ctx, b);
    let c_expr = finite_domain_bool_value(ctx, c);
    let h12_ty = finite_domain_ne_f(ctx, f, b_expr, c_expr);
    let with_h12 = ctx.kernel.lam(anon, h12_ty, proof, BinderInfo::Default);
    let h02_ty = finite_domain_ne_f(ctx, f, a_expr, c_expr);
    let with_h02 = ctx.kernel.lam(anon, h02_ty, with_h12, BinderInfo::Default);
    let h01_ty = finite_domain_ne_f(ctx, f, a_expr, b_expr);
    ctx.kernel.lam(anon, h01_ty, with_h02, BinderInfo::Default)
}

fn finite_domain_c_motive(ctx: &mut ReconstructCtx, f: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let anon = ctx.kernel.anon();
    let bool_ty = finite_domain_bool_ty(ctx);
    let false_ = finite_domain_false(ctx);

    let c_for_h12 = ctx.kernel.bvar(2);
    let h12_ty = finite_domain_ne_f(ctx, f, b, c_for_h12);
    let body = ctx.kernel.pi(anon, h12_ty, false_, BinderInfo::Default);

    let c_for_h02 = ctx.kernel.bvar(1);
    let h02_ty = finite_domain_ne_f(ctx, f, a, c_for_h02);
    let body = ctx.kernel.pi(anon, h02_ty, body, BinderInfo::Default);

    let h01_ty = finite_domain_ne_f(ctx, f, a, b);
    let body = ctx.kernel.pi(anon, h01_ty, body, BinderInfo::Default);
    ctx.kernel.lam(anon, bool_ty, body, BinderInfo::Default)
}

fn finite_domain_c_cases(ctx: &mut ReconstructCtx, f: ExprId, a: bool, b: bool) -> ExprId {
    let a_expr = finite_domain_bool_value(ctx, a);
    let b_expr = finite_domain_bool_value(ctx, b);
    let motive = finite_domain_c_motive(ctx, f, a_expr, b_expr);
    let true_case = finite_domain_leaf(ctx, f, a, b, true);
    let false_case = finite_domain_leaf(ctx, f, a, b, false);
    finite_domain_bool_rec(ctx, motive, true_case, false_case)
}

fn finite_domain_b_motive(ctx: &mut ReconstructCtx, f: ExprId, a: ExprId) -> ExprId {
    let anon = ctx.kernel.anon();
    let bool_ty = finite_domain_bool_ty(ctx);
    let false_ = finite_domain_false(ctx);

    let b_for_h12 = ctx.kernel.bvar(3);
    let c_for_h12 = ctx.kernel.bvar(2);
    let h12_ty = finite_domain_ne_f(ctx, f, b_for_h12, c_for_h12);
    let body = ctx.kernel.pi(anon, h12_ty, false_, BinderInfo::Default);

    let c_for_h02 = ctx.kernel.bvar(1);
    let h02_ty = finite_domain_ne_f(ctx, f, a, c_for_h02);
    let body = ctx.kernel.pi(anon, h02_ty, body, BinderInfo::Default);

    let b_for_h01 = ctx.kernel.bvar(1);
    let h01_ty = finite_domain_ne_f(ctx, f, a, b_for_h01);
    let body = ctx.kernel.pi(anon, h01_ty, body, BinderInfo::Default);

    let body = ctx.kernel.pi(anon, bool_ty, body, BinderInfo::Default);
    ctx.kernel.lam(anon, bool_ty, body, BinderInfo::Default)
}

fn finite_domain_b_cases(ctx: &mut ReconstructCtx, f: ExprId, a: bool) -> ExprId {
    let a_expr = finite_domain_bool_value(ctx, a);
    let motive = finite_domain_b_motive(ctx, f, a_expr);
    let true_case = finite_domain_c_cases(ctx, f, a, true);
    let false_case = finite_domain_c_cases(ctx, f, a, false);
    finite_domain_bool_rec(ctx, motive, true_case, false_case)
}

fn finite_domain_a_motive(ctx: &mut ReconstructCtx, f: ExprId) -> ExprId {
    let anon = ctx.kernel.anon();
    let bool_ty = finite_domain_bool_ty(ctx);
    let false_ = finite_domain_false(ctx);

    let b_for_h12 = ctx.kernel.bvar(3);
    let c_for_h12 = ctx.kernel.bvar(2);
    let h12_ty = finite_domain_ne_f(ctx, f, b_for_h12, c_for_h12);
    let body = ctx.kernel.pi(anon, h12_ty, false_, BinderInfo::Default);

    let a_for_h02 = ctx.kernel.bvar(3);
    let c_for_h02 = ctx.kernel.bvar(1);
    let h02_ty = finite_domain_ne_f(ctx, f, a_for_h02, c_for_h02);
    let body = ctx.kernel.pi(anon, h02_ty, body, BinderInfo::Default);

    let a_for_h01 = ctx.kernel.bvar(2);
    let b_for_h01 = ctx.kernel.bvar(1);
    let h01_ty = finite_domain_ne_f(ctx, f, a_for_h01, b_for_h01);
    let body = ctx.kernel.pi(anon, h01_ty, body, BinderInfo::Default);

    let body = ctx.kernel.pi(anon, bool_ty, body, BinderInfo::Default);
    let body = ctx.kernel.pi(anon, bool_ty, body, BinderInfo::Default);
    ctx.kernel.lam(anon, bool_ty, body, BinderInfo::Default)
}

fn build_bool_pigeonhole3(ctx: &mut ReconstructCtx, f: ExprId) -> ExprId {
    let motive = finite_domain_a_motive(ctx, f);
    let true_case = finite_domain_b_cases(ctx, f, true);
    let false_case = finite_domain_b_cases(ctx, f, false);
    finite_domain_bool_rec(ctx, motive, true_case, false_case)
}

fn reconstruct_reflexive_disequality_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let term = reflexive_disequality_assertion(arena, assertions).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "reflexive_disequality".to_owned(),
            detail: "expected a top-level assertion `not (= t t)`".to_owned(),
        }
    })?;

    let mut ctx = ReconstructCtx::new();
    let t = reflexive_disequality_term_expr(&mut ctx, term);
    let eq_prop = ctx.mk_eq(t, t);
    let diseq_prop = ctx.mk_not(eq_prop);
    let diseq = fresh_axiom(&mut ctx, diseq_prop, "assume")?;
    let refl = ctx.mk_eq_refl(t);
    let proof = ctx.kernel.app(diseq, refl);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

fn reflexive_disequality_term_expr(ctx: &mut ReconstructCtx, term: TermId) -> ExprId {
    let name = ctx.atom_const(&format!("reflexive_diseq_term_{}", term.index()));
    ctx.kernel.const_(name, vec![])
}

fn reconstruct_term_identity_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::term_identity::term_identity_refutation(arena, assertions).ok_or_else(|| {
            ReconstructError::MalformedStep {
                rule: "term_identity".to_owned(),
                detail: "expected negation of a checked term identity".to_owned(),
            }
        })?;

    let mut ctx = ReconstructCtx::new();
    let lhs = term_identity_term_expr(&mut ctx, cert.lhs);
    let rhs = term_identity_term_expr(&mut ctx, cert.rhs);
    let eq_prop = ctx.mk_eq(lhs, rhs);
    let eq_proof = fresh_axiom(&mut ctx, eq_prop, "term_identity")?;
    let diseq_prop = ctx.mk_not(eq_prop);
    let diseq = fresh_axiom(&mut ctx, diseq_prop, "assume")?;
    let proof = ctx.kernel.app(diseq, eq_proof);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

fn term_identity_term_expr(ctx: &mut ReconstructCtx, term: TermId) -> ExprId {
    let name = ctx.atom_const(&format!("term_identity_term_{}", term.index()));
    ctx.kernel.const_(name, vec![])
}

fn reconstruct_bool_simplification_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::bool_simplify::bool_simplification_refutation(arena, assertions).ok_or_else(
        || ReconstructError::MalformedStep {
            rule: "bool_simplification".to_owned(),
            detail: "expected an assertion that checked Boolean simplification reduces to false"
                .to_owned(),
        },
    )?;

    reconstruct_checked_structural_certificate_to_lean_module(
        &format!("bool_simplification_{}", cert.assertion.index()),
        "bool_simplification",
    )
}

fn reconstruct_bool_uf_exhaustive_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::ufbv_finite::bool_uf_exhaustive_refutation(arena, assertions).ok_or_else(|| {
            ReconstructError::MalformedStep {
                rule: "bool_uf_exhaustive".to_owned(),
                detail: "expected a tiny unsatisfiable Boolean-UF formula".to_owned(),
            }
        })?;
    if cert.functions.is_empty() || cert.cases == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "bool_uf_exhaustive".to_owned(),
            detail: "Boolean-UF certificate carried no function interpretation space".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "bool_uf_exhaustive_assertions",
        "bool_uf_exhaustive",
    )
}

fn reconstruct_bool_euf_exhaustive_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::bool_euf::bool_euf_exhaustive_refutation(arena, assertions).ok_or_else(|| {
            ReconstructError::MalformedStep {
                rule: "bool_euf_exhaustive".to_owned(),
                detail: "expected a Boolean-structured EUF refutation".to_owned(),
            }
        })?;
    if cert.atoms.is_empty() {
        return Err(ReconstructError::MalformedStep {
            rule: "bool_euf_exhaustive".to_owned(),
            detail: "Boolean-EUF certificate carried no equality atoms".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "bool_euf_exhaustive_assertions",
        "bool_euf_exhaustive",
    )
}

fn reconstruct_bool_euf_online_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::bool_euf::bool_euf_online_refutation(arena, assertions).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "bool_euf_online".to_owned(),
            detail: "expected an online Boolean-EUF refutation".to_owned(),
        }
    })?;
    if cert.atoms == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "bool_euf_online".to_owned(),
            detail: "online Boolean-EUF certificate carried no equality atoms".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "bool_euf_online_assertions",
        "bool_euf_online",
    )
}

fn reconstruct_uf_arith_congruence_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::uf_arith::uf_arith_congruence_refutation(arena, assertions).ok_or_else(|| {
            ReconstructError::MalformedStep {
                rule: "uf_arith_congruence".to_owned(),
                detail: "expected a mixed UF+arithmetic congruence refutation".to_owned(),
            }
        })?;
    if cert.congruence_consequents == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "uf_arith_congruence".to_owned(),
            detail: "certificate carried no arithmetic congruence consequents".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "uf_arith_congruence_assertions",
        "uf_arith_congruence",
    )
}

fn reconstruct_datatype_structural_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    if crate::datatype_acyclicity::datatype_structural_refutation(arena, assertions).is_none() {
        return Err(ReconstructError::MalformedStep {
            rule: "datatype_structural".to_owned(),
            detail: "datatype structural refutation failed".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "datatype_structural_assertions",
        "datatype_structural",
    )
}

fn reconstruct_finite_domain_enum_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    match crate::certify_finite_bv_by_enumeration(arena, assertions, FINITE_DOMAIN_ENUM_CERT_BITS) {
        Ok(crate::CertifyOutcome::CertifiedUnsat { .. }) => {}
        Ok(crate::CertifyOutcome::Satisfiable(_)) => {
            return Err(ReconstructError::MalformedStep {
                rule: "finite_domain_enum".to_owned(),
                detail: "finite-domain enumeration found a satisfying assignment".to_owned(),
            });
        }
        Ok(crate::CertifyOutcome::DomainTooLarge { total_bits }) => {
            return Err(ReconstructError::MalformedStep {
                rule: "finite_domain_enum".to_owned(),
                detail: format!(
                    "finite-domain enumeration needs {total_bits} bits, above the proof budget"
                ),
            });
        }
        Err(error) => {
            return Err(ReconstructError::MalformedStep {
                rule: "finite_domain_enum".to_owned(),
                detail: format!("finite-domain enumeration certificate failed: {error}"),
            });
        }
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "finite_domain_enum_assertions",
        "finite_domain_enum",
    )
}

fn reconstruct_term_level_enum_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    match crate::certify_qf_bv_by_enumeration(arena, assertions, FINITE_DOMAIN_ENUM_CERT_BITS) {
        Ok(crate::CertifyOutcome::CertifiedUnsat { .. }) => {}
        Ok(crate::CertifyOutcome::Satisfiable(_)) => {
            return Err(ReconstructError::MalformedStep {
                rule: "term_level_enum".to_owned(),
                detail: "term-level enumeration found a satisfying assignment".to_owned(),
            });
        }
        Ok(crate::CertifyOutcome::DomainTooLarge { total_bits }) => {
            return Err(ReconstructError::MalformedStep {
                rule: "term_level_enum".to_owned(),
                detail: format!(
                    "term-level enumeration needs {total_bits} bits, above the proof budget"
                ),
            });
        }
        Err(error) => {
            return Err(ReconstructError::MalformedStep {
                rule: "term_level_enum".to_owned(),
                detail: format!("term-level enumeration certificate failed: {error}"),
            });
        }
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "term_level_enum_assertions",
        "term_level_enum",
    )
}

fn reconstruct_bv_defined_enum_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    if crate::bv_defined_enum::bv_defined_enum_refutation(arena, assertions).is_none() {
        return Err(ReconstructError::MalformedStep {
            rule: "bv_defined_enum".to_owned(),
            detail: "definition-aware BV enumeration certificate failed".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "bv_defined_enum_assertions",
        "bv_defined_enum",
    )
}

fn reconstruct_set_cardinality_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    if crate::set_cardinality::set_cardinality_refutation(arena, assertions).is_none() {
        return Err(ReconstructError::MalformedStep {
            rule: "set_cardinality".to_owned(),
            detail: "set-cardinality certificate failed".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "set_cardinality_assertions",
        "set_cardinality",
    )
}

fn reconstruct_bv_forall_nonconstant_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::bv_forall_nonconstant::bv_forall_nonconstant_refutation(arena, assertions)
        .ok_or_else(|| ReconstructError::MalformedStep {
            rule: "bv_forall_nonconstant".to_owned(),
            detail: "expected a checked quantified-BV non-constant refutation".to_owned(),
        })?;
    if !crate::bv_forall_nonconstant::bv_forall_nonconstant_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == cert)
    {
        return Err(ReconstructError::MalformedStep {
            rule: "bv_forall_nonconstant".to_owned(),
            detail: "quantified-BV non-constant certificate did not recheck".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "bv_forall_nonconstant_assertions",
        "bv_forall_nonconstant",
    )
}

fn reconstruct_bv_uf_local_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::bv_uf_local::bv_uf_local_refutation(arena, assertions).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "bv_uf_local".to_owned(),
            detail: "expected a checked local BV+UF refutation".to_owned(),
        }
    })?;
    if !crate::bv_uf_local::bv_uf_local_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == cert)
    {
        return Err(ReconstructError::MalformedStep {
            rule: "bv_uf_local".to_owned(),
            detail: "local BV+UF certificate did not recheck".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "bv_uf_local_assertions",
        "bv_uf_local",
    )
}

fn reconstruct_lra_dpll_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let mut scratch = arena.clone();
    let refutation = match crate::dpll_t::certify_lra_dpll_unsat(
        &mut scratch,
        assertions,
        &crate::backend::SolverConfig::default(),
    ) {
        Ok(crate::dpll_t::LraDpllOutcome::Unsat(refutation)) => refutation,
        Ok(crate::dpll_t::LraDpllOutcome::Sat(_)) => {
            return Err(ReconstructError::MalformedStep {
                rule: "lra_dpll".to_owned(),
                detail: "lazy-SMT certificate returned sat, not unsat".to_owned(),
            });
        }
        Ok(crate::dpll_t::LraDpllOutcome::Unknown(reason)) => {
            return Err(ReconstructError::MalformedStep {
                rule: "lra_dpll".to_owned(),
                detail: format!("lazy-SMT certificate returned unknown: {}", reason.detail),
            });
        }
        Err(error) => {
            return Err(ReconstructError::MalformedStep {
                rule: "lra_dpll".to_owned(),
                detail: format!("lazy-SMT certificate failed: {error}"),
            });
        }
    };
    if !refutation
        .verify(&scratch)
        .map_err(|error| ReconstructError::MalformedStep {
            rule: "lra_dpll".to_owned(),
            detail: format!("lazy-SMT refutation self-check failed: {error}"),
        })?
    {
        return Err(ReconstructError::MalformedStep {
            rule: "lra_dpll".to_owned(),
            detail: "lazy-SMT refutation did not verify".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "lra_dpll_assertions",
        "lra_dpll",
    )
}

fn reconstruct_arith_dpll_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let mut scratch = arena.clone();
    let refutation = match crate::dpll_lia::certify_arith_dpll_unsat(
        &mut scratch,
        assertions,
        &crate::backend::SolverConfig::default(),
    ) {
        Ok(crate::dpll_lia::ArithDpllOutcome::Unsat(refutation)) => refutation,
        Ok(crate::dpll_lia::ArithDpllOutcome::Sat(_)) => {
            return Err(ReconstructError::MalformedStep {
                rule: "arith_dpll".to_owned(),
                detail: "arithmetic lazy-SMT certificate returned sat, not unsat".to_owned(),
            });
        }
        Ok(crate::dpll_lia::ArithDpllOutcome::Unknown(reason)) => {
            return Err(ReconstructError::MalformedStep {
                rule: "arith_dpll".to_owned(),
                detail: format!(
                    "arithmetic lazy-SMT certificate returned unknown: {}",
                    reason.detail
                ),
            });
        }
        Err(error) => {
            return Err(ReconstructError::MalformedStep {
                rule: "arith_dpll".to_owned(),
                detail: format!("arithmetic lazy-SMT certificate failed: {error}"),
            });
        }
    };
    if !refutation
        .verify(&scratch)
        .map_err(|error| ReconstructError::MalformedStep {
            rule: "arith_dpll".to_owned(),
            detail: format!("arithmetic lazy-SMT refutation self-check failed: {error}"),
        })?
    {
        return Err(ReconstructError::MalformedStep {
            rule: "arith_dpll".to_owned(),
            detail: "arithmetic lazy-SMT refutation did not verify".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "arith_dpll_assertions",
        "arith_dpll",
    )
}

fn reconstruct_bounded_int_blast_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::auto::certify_bounded_int_blast(arena, assertions).map_err(|error| {
        ReconstructError::MalformedStep {
            rule: "bounded_int_blast".to_owned(),
            detail: format!("bounded-int-blast certificate failed: {error}"),
        }
    })?;
    let cert = cert.ok_or_else(|| ReconstructError::MalformedStep {
        rule: "bounded_int_blast".to_owned(),
        detail: "expected a proven-box bounded integer blast refutation".to_owned(),
    })?;
    if !cert
        .recheck(arena, assertions)
        .map_err(|error| ReconstructError::MalformedStep {
            rule: "bounded_int_blast".to_owned(),
            detail: format!("bounded-int-blast certificate recheck failed: {error}"),
        })?
    {
        return Err(ReconstructError::MalformedStep {
            rule: "bounded_int_blast".to_owned(),
            detail: "bounded-int-blast certificate did not recheck".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "bounded_int_blast_assertions",
        "bounded_int_blast",
    )
}

fn reconstruct_nra_even_power_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::nra_even_power::nra_even_power_refutation(arena, assertions).ok_or_else(|| {
            ReconstructError::MalformedStep {
                rule: "nra_even_power".to_owned(),
                detail: "expected a checked even-power NRA refutation".to_owned(),
            }
        })?;
    if !crate::nra_even_power::nra_even_power_refutation(arena, assertions)
        .is_some_and(|fresh| fresh == cert)
    {
        return Err(ReconstructError::MalformedStep {
            rule: "nra_even_power".to_owned(),
            detail: "even-power NRA certificate did not recheck".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "nra_even_power_assertions",
        "nra_even_power",
    )
}

fn reconstruct_array_axiom_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_axiom::array_axiom_refutation(arena, assertions).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "array_axiom".to_owned(),
            detail: "expected negation of a checked array axiom schema".to_owned(),
        }
    })?;

    let mut ctx = ReconstructCtx::new();
    let lhs = array_axiom_term_expr(&mut ctx, cert.lhs);
    let rhs = array_axiom_term_expr(&mut ctx, cert.rhs);
    let eq_prop = ctx.mk_eq(lhs, rhs);
    let eq_proof = fresh_axiom(&mut ctx, eq_prop, "array_axiom")?;
    let diseq_prop = ctx.mk_not(eq_prop);
    let diseq = fresh_axiom(&mut ctx, diseq_prop, "assume")?;
    let proof = ctx.kernel.app(diseq, eq_proof);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

fn array_axiom_term_expr(ctx: &mut ReconstructCtx, term: TermId) -> ExprId {
    let name = ctx.atom_const(&format!("array_axiom_term_{}", term.index()));
    ctx.kernel.const_(name, vec![])
}

fn reconstruct_const_array_default_mismatch_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::abv::const_array_default_mismatch_refutation(arena, assertions).ok_or_else(
        || ReconstructError::MalformedStep {
            rule: "const_array_default_mismatch".to_owned(),
            detail: "expected a checked const-array default mismatch refutation".to_owned(),
        },
    )?;
    if !cert.recheck(arena, assertions) {
        return Err(ReconstructError::MalformedStep {
            rule: "const_array_default_mismatch".to_owned(),
            detail: "const-array default mismatch certificate did not recheck".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "const_array_default_mismatch_assertions",
        "const_array_default_mismatch",
    )
}

fn reconstruct_store_chain_readback_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::abv::store_chain_readback_refutation(arena, assertions).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "store_chain_readback".to_owned(),
            detail: "expected a checked store-chain readback refutation".to_owned(),
        }
    })?;
    if !cert.recheck(arena, assertions) {
        return Err(ReconstructError::MalformedStep {
            rule: "store_chain_readback".to_owned(),
            detail: "store-chain readback certificate did not recheck".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "store_chain_readback_assertions",
        "store_chain_readback",
    )
}

fn reconstruct_cross_store_array_disequality_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::abv::cross_store_array_disequality_refutation(arena, assertions).ok_or_else(
        || ReconstructError::MalformedStep {
            rule: "cross_store_array_disequality".to_owned(),
            detail: "expected a checked cross-store array disequality refutation".to_owned(),
        },
    )?;
    if !cert.recheck(arena, assertions) {
        return Err(ReconstructError::MalformedStep {
            rule: "cross_store_array_disequality".to_owned(),
            detail: "cross-store array disequality certificate did not recheck".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "cross_store_array_disequality_assertions",
        "cross_store_array_disequality",
    )
}

pub(super) fn reconstruct_checked_structural_certificate_to_lean_module(
    prop_stem: &str,
    refuter_role: &str,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();
    let prop_name = ctx.prop_atom_const(prop_stem);
    let prop = ctx.kernel.const_(prop_name, vec![]);
    let asserted = fresh_axiom(&mut ctx, prop, "assume")?;
    let refuter_prop = ctx.mk_not(prop);
    let refuter = fresh_axiom(&mut ctx, refuter_prop, refuter_role)?;
    let proof = ctx.kernel.app(refuter, asserted);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

fn reconstruct_bv_abstraction_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::array_bv_abs::bv_abstraction_refutation(arena, assertions).ok_or_else(|| {
            ReconstructError::MalformedStep {
                rule: "bv_abstraction".to_owned(),
                detail: "expected certified-unsat scalar BV abstraction".to_owned(),
            }
        })?;
    if cert.abstracted_terms.is_empty() {
        return Err(ReconstructError::MalformedStep {
            rule: "bv_abstraction".to_owned(),
            detail: "BV abstraction certificate carried no abstracted terms".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "bv_abstraction_assertions",
        "bv_abstraction",
    )
}

fn reconstruct_two_byte_memcpy_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::array_memcpy::two_byte_memcpy_refutation(arena, assertions).ok_or_else(|| {
            ReconstructError::MalformedStep {
                rule: "two_byte_memcpy".to_owned(),
                detail: "expected guarded two-byte memcpy refutation".to_owned(),
            }
        })?;
    if cert.index_width == 0 || cert.element_width == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "two_byte_memcpy".to_owned(),
            detail: "memcpy certificate carried a zero-width sort".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "two_byte_memcpy_assertion",
        "two_byte_memcpy",
    )
}

fn reconstruct_two_element_bubble_sort_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_sort2::two_element_bubble_sort_refutation(arena, assertions)
        .ok_or_else(|| ReconstructError::MalformedStep {
            rule: "two_element_bubble_sort".to_owned(),
            detail: "expected guarded two-element bubble-sort refutation".to_owned(),
        })?;
    if cert.index_width == 0 || cert.element_width == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "two_element_bubble_sort".to_owned(),
            detail: "bubble-sort certificate carried a zero-width sort".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "two_element_bubble_sort_assertion",
        "two_element_bubble_sort",
    )
}

fn reconstruct_two_element_selection_sort_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_sort2::two_element_selection_sort_refutation(arena, assertions)
        .ok_or_else(|| ReconstructError::MalformedStep {
            rule: "two_element_selection_sort".to_owned(),
            detail: "expected guarded two-element selection-sort refutation".to_owned(),
        })?;
    if cert.index_width == 0 || cert.element_width == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "two_element_selection_sort".to_owned(),
            detail: "selection-sort certificate carried a zero-width sort".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "two_element_selection_sort_assertion",
        "two_element_selection_sort",
    )
}

fn reconstruct_aligned_write_chain_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert =
        crate::array_write_chain::aligned_write_chain_commutation_refutation(arena, assertions)
            .ok_or_else(|| ReconstructError::MalformedStep {
                rule: "aligned_write_chain".to_owned(),
                detail: "expected guarded aligned write-chain commutation refutation".to_owned(),
            })?;
    if cert.lanes == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "aligned_write_chain".to_owned(),
            detail: "write-chain certificate carried no lanes".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "aligned_write_chain_assertion",
        "aligned_write_chain",
    )
}

fn reconstruct_two_cell_xor_swap_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_xor_swap::two_cell_xor_swap_refutation(arena, assertions).ok_or_else(
        || ReconstructError::MalformedStep {
            rule: "two_cell_xor_swap".to_owned(),
            detail: "expected two-cell XOR-swap permutation refutation".to_owned(),
        },
    )?;
    if cert.index_width == 0 || cert.element_width == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "two_cell_xor_swap".to_owned(),
            detail: "XOR-swap certificate carried a zero-width sort".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "two_cell_xor_swap_assertion",
        "two_cell_xor_swap",
    )
}

fn reconstruct_two_byte_xor_swap_roundtrip_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_xor_swap::two_byte_xor_swap_roundtrip_refutation(arena, assertions)
        .ok_or_else(|| ReconstructError::MalformedStep {
            rule: "two_byte_xor_swap_roundtrip".to_owned(),
            detail: "expected guarded two-byte XOR-swap round-trip refutation".to_owned(),
        })?;
    if cert.index_width == 0 || cert.element_width == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "two_byte_xor_swap_roundtrip".to_owned(),
            detail: "XOR-swap round-trip certificate carried a zero-width sort".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "two_byte_xor_swap_roundtrip_assertion",
        "two_byte_xor_swap_roundtrip",
    )
}

fn reconstruct_binary_search16_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_binary_search::binary_search16_refutation(arena, assertions)
        .ok_or_else(|| ReconstructError::MalformedStep {
            rule: "binary_search16".to_owned(),
            detail: "expected generated 16-element binary-search miss refutation".to_owned(),
        })?;
    if cert.index_width == 0 || cert.element_width == 0 || cert.probes.is_empty() {
        return Err(ReconstructError::MalformedStep {
            rule: "binary_search16".to_owned(),
            detail: "binary-search certificate carried an empty probe or zero-width sort"
                .to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "binary_search16_assertion",
        "binary_search16",
    )
}

fn reconstruct_fifo_bc04_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_fifo::fifo_bc04_refutation(arena, assertions).ok_or_else(|| {
        ReconstructError::MalformedStep {
            rule: "fifo_bc04".to_owned(),
            detail: "expected generated five-cycle FIFO equivalence refutation".to_owned(),
        }
    })?;
    if cert.bound == 0 || cert.index_width == 0 || cert.element_width == 0 {
        return Err(ReconstructError::MalformedStep {
            rule: "fifo_bc04".to_owned(),
            detail: "FIFO certificate carried a zero bound or zero-width sort".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        "fifo_bc04_assertion",
        "fifo_bc04",
    )
}

fn reconstruct_bool_array_read_collapse_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_finite::bool_array_read_collapse_refutation(arena, assertions)
        .ok_or_else(|| ReconstructError::MalformedStep {
            rule: "bool_array_read_collapse".to_owned(),
            detail: "expected equal Bool-index concrete reads plus a read disequality".to_owned(),
        })?;
    if !cert.recheck(arena, assertions) {
        return Err(ReconstructError::MalformedStep {
            rule: "bool_array_read_collapse".to_owned(),
            detail: "Bool-array read-collapse certificate did not recheck".to_owned(),
        });
    }

    reconstruct_checked_structural_certificate_to_lean_module(
        &format!(
            "bool_array_read_collapse_{}_{}_{}",
            cert.array.index(),
            cert.concrete_equality.index(),
            cert.disequality.index()
        ),
        "bool_array_read_collapse",
    )
}

fn reconstruct_finite_array_extensionality_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<String, ReconstructError> {
    let cert = crate::array_finite::finite_array_extensionality_refutation(arena, assertions)
        .ok_or_else(|| ReconstructError::MalformedStep {
            rule: "finite_array_extensionality".to_owned(),
            detail: "expected all finite BV-index reads plus an array disequality".to_owned(),
        })?;
    if cert.read_equalities.is_empty() {
        return Err(ReconstructError::MalformedStep {
            rule: "finite_array_extensionality".to_owned(),
            detail: "finite array extensionality certificate carried no reads".to_owned(),
        });
    }

    let mut ctx = ReconstructCtx::new();
    let mut props = Vec::with_capacity(cert.read_equalities.len());
    let mut witnesses = Vec::with_capacity(cert.read_equalities.len());
    for read in &cert.read_equalities {
        let lhs = finite_array_read_expr(&mut ctx, read.lhs_read);
        let rhs = finite_array_read_expr(&mut ctx, read.rhs_read);
        let prop = ctx.mk_eq(lhs, rhs);
        let witness = fresh_axiom(&mut ctx, prop, "assume")?;
        props.push(prop);
        witnesses.push(witness);
    }

    let array_eq_prop = finite_array_extensional_eq_prop(&mut ctx, &props);
    let array_eq_proof = finite_array_extensional_eq_proof(&mut ctx, &props, &witnesses);
    let diseq_prop = ctx.mk_not(array_eq_prop);
    let diseq = fresh_axiom(&mut ctx, diseq_prop, "assume")?;
    let proof = ctx.kernel.app(diseq, array_eq_proof);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

fn finite_array_read_expr(ctx: &mut ReconstructCtx, term: TermId) -> ExprId {
    let name = ctx.atom_const(&format!("finite_array_read_{}", term.index()));
    ctx.kernel.const_(name, vec![])
}

fn finite_array_extensional_eq_prop(ctx: &mut ReconstructCtx, props: &[ExprId]) -> ExprId {
    if props.len() == 1 {
        props[0]
    } else {
        and_chain_prop_of(ctx, props)
    }
}

fn finite_array_extensional_eq_proof(
    ctx: &mut ReconstructCtx,
    props: &[ExprId],
    witnesses: &[ExprId],
) -> ExprId {
    if witnesses.len() == 1 {
        witnesses[0]
    } else {
        and_intro_fold(ctx, props, witnesses)
    }
}

pub(super) fn reconstruct_direct_structural_fragment_to_lean_module(
    fragment: ProofFragment,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<String>, ReconstructError> {
    let source = match fragment {
        ProofFragment::ReflexiveDisequality => {
            reconstruct_reflexive_disequality_to_lean_module(arena, assertions)?
        }
        ProofFragment::TermIdentity => reconstruct_term_identity_to_lean_module(arena, assertions)?,
        ProofFragment::BoolSimplification => {
            reconstruct_bool_simplification_to_lean_module(arena, assertions)?
        }
        ProofFragment::LraDpll => reconstruct_lra_dpll_to_lean_module(arena, assertions)?,
        ProofFragment::ArithDpll => reconstruct_arith_dpll_to_lean_module(arena, assertions)?,
        ProofFragment::BoundedIntBlast => {
            reconstruct_bounded_int_blast_to_lean_module(arena, assertions)?
        }
        ProofFragment::NraEvenPower => {
            reconstruct_nra_even_power_to_lean_module(arena, assertions)?
        }
        ProofFragment::FiniteDomainPigeonhole => {
            reconstruct_finite_domain_pigeonhole_to_lean_module(arena, assertions)?
        }
        ProofFragment::BoolUfExhaustive => {
            reconstruct_bool_uf_exhaustive_to_lean_module(arena, assertions)?
        }
        ProofFragment::BoolEufExhaustive => {
            reconstruct_bool_euf_exhaustive_to_lean_module(arena, assertions)?
        }
        ProofFragment::BoolEufOnline => {
            reconstruct_bool_euf_online_to_lean_module(arena, assertions)?
        }
        ProofFragment::UfArithCongruence => {
            reconstruct_uf_arith_congruence_to_lean_module(arena, assertions)?
        }
        ProofFragment::DatatypeStructural => {
            reconstruct_datatype_structural_to_lean_module(arena, assertions)?
        }
        ProofFragment::FiniteDomainEnum => {
            reconstruct_finite_domain_enum_to_lean_module(arena, assertions)?
        }
        ProofFragment::TermLevelEnum => {
            reconstruct_term_level_enum_to_lean_module(arena, assertions)?
        }
        ProofFragment::BvDefinedEnum => {
            reconstruct_bv_defined_enum_to_lean_module(arena, assertions)?
        }
        ProofFragment::SetCardinality => {
            reconstruct_set_cardinality_to_lean_module(arena, assertions)?
        }
        ProofFragment::BvForallNonconstant => {
            reconstruct_bv_forall_nonconstant_to_lean_module(arena, assertions)?
        }
        ProofFragment::BvUfLocal => reconstruct_bv_uf_local_to_lean_module(arena, assertions)?,
        ProofFragment::ArrayAxiom => reconstruct_array_axiom_to_lean_module(arena, assertions)?,
        ProofFragment::ConstArrayDefaultMismatch => {
            reconstruct_const_array_default_mismatch_to_lean_module(arena, assertions)?
        }
        ProofFragment::StoreChainReadback => {
            reconstruct_store_chain_readback_to_lean_module(arena, assertions)?
        }
        ProofFragment::CrossStoreArrayDisequality => {
            reconstruct_cross_store_array_disequality_to_lean_module(arena, assertions)?
        }
        ProofFragment::BoolArrayReadCollapse => {
            reconstruct_bool_array_read_collapse_to_lean_module(arena, assertions)?
        }
        ProofFragment::FiniteArrayExtensionality => {
            reconstruct_finite_array_extensionality_to_lean_module(arena, assertions)?
        }
        ProofFragment::BvAbstraction => {
            reconstruct_bv_abstraction_to_lean_module(arena, assertions)?
        }
        ProofFragment::TwoByteMemcpy => {
            reconstruct_two_byte_memcpy_to_lean_module(arena, assertions)?
        }
        ProofFragment::TwoElementBubbleSort => {
            reconstruct_two_element_bubble_sort_to_lean_module(arena, assertions)?
        }
        ProofFragment::TwoElementSelectionSort => {
            reconstruct_two_element_selection_sort_to_lean_module(arena, assertions)?
        }
        ProofFragment::TwoCellXorSwap => {
            reconstruct_two_cell_xor_swap_to_lean_module(arena, assertions)?
        }
        ProofFragment::TwoByteXorSwapRoundtrip => {
            reconstruct_two_byte_xor_swap_roundtrip_to_lean_module(arena, assertions)?
        }
        ProofFragment::BinarySearch16 => {
            reconstruct_binary_search16_to_lean_module(arena, assertions)?
        }
        ProofFragment::FifoBc04 => reconstruct_fifo_bc04_to_lean_module(arena, assertions)?,
        ProofFragment::AlignedWriteChainCommutation => {
            reconstruct_aligned_write_chain_to_lean_module(arena, assertions)?
        }
        _ => return Ok(None),
    };
    Ok(Some(source))
}
