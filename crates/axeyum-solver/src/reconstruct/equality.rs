//! Kernel-checked reconstruction for Alethe equality rules.

use super::{
    AletheLit, AletheTerm, BinderInfo, Declaration, ExprId, ReconstructCtx, ReconstructError,
    as_negated_eq, as_positive_eq, check_against,
};

/// Reconstruct an equality-rule step into a kernel-checked Lean proof term.
///
/// `premises` are the proof terms (already-built Lean [`ExprId`]s) for the step's
/// premises, in order; `conclusion` is the step's conclusion **clause** (the
/// step's `(cl …)` literals). The returned proof term is `infer`-checked by the
/// kernel and [`axeyum_lean_kernel::Kernel::def_eq`]-compared to the translated
/// conclusion proposition; on success the proof term is returned.
///
/// Supported `rule`s (this slice):
///
/// - `eq_reflexive` ⊢ `(cl (= a a))` ⇒ `Eq.refl.{1} α a` (no premises);
/// - `eq_symmetric` ⊢ `(cl (not (= a b)) (= b a))`, premise `h : Eq α a b`
///   ⇒ `Eq.rec` transport with motive `fun x _ => Eq α x a`;
/// - `eq_transitive` ⊢ `(cl (not (= a b)) (not (= b c)) (= a c))`, premises
///   `h1 : Eq α a b`, `h2 : Eq α b c` ⇒ `Eq.rec` transport of `h1` along `h2`
///   with motive `fun x _ => Eq α a x`.
///
/// Note the Alethe `eq_*` conclusion clauses carry the **negated hypotheses**
/// inline (`(not (= a b))`); the *positive* equality is the last literal. For
/// reconstruction we extract that positive equality (the actual proposition the
/// rule proves) and the hypothesis equalities from the leading negated literals,
/// rather than treating `premises` as already-clausal — so a self-contained
/// `eq_symmetric`/`eq_transitive` step (premise-free in Alethe) is reconstructed
/// by reading its own clause, while a step threaded with explicit premise proofs
/// supplies those proofs through `premises`.
///
/// # Errors
///
/// Returns [`ReconstructError::UnsupportedRule`] for a non-equality rule,
/// [`ReconstructError::UnsupportedTerm`] for an out-of-scope conclusion term,
/// [`ReconstructError::MalformedStep`] for a clause/premise shape that does not
/// match the rule, and [`ReconstructError::KernelRejected`] when the kernel's
/// `infer` fails or the inferred proposition is not `def_eq` to the conclusion.
pub fn reconstruct_eq_step(
    ctx: &mut ReconstructCtx,
    rule: &str,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    match rule {
        "eq_reflexive" => reconstruct_eq_reflexive(ctx, conclusion),
        "eq_symmetric" => reconstruct_eq_symmetric(ctx, premises, conclusion),
        "eq_transitive" => reconstruct_eq_transitive(ctx, premises, conclusion),
        other => Err(ReconstructError::UnsupportedRule {
            rule: other.to_owned(),
        }),
    }
}

/// `eq_reflexive` ⊢ `(cl (= a a))` ⇒ `Eq.refl.{1} α a`.
fn reconstruct_eq_reflexive(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    let [lit] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_reflexive".to_owned(),
            detail: format!("expected one literal, found {}", conclusion.len()),
        });
    };
    let Some((a_t, b_t)) = as_positive_eq(lit) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_reflexive".to_owned(),
            detail: "conclusion is not a positive equality `(= a a)`".to_owned(),
        });
    };
    if a_t != b_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_reflexive".to_owned(),
            detail: "reflexivity conclusion `(= a b)` has a != b".to_owned(),
        });
    }
    let a = ctx.alethe_term_to_expr(a_t)?;
    let proof = ctx.mk_eq_refl(a);
    let expected = ctx.mk_eq(a, a);
    check_against(ctx, "eq_reflexive", proof, expected)
}

/// `eq_symmetric` ⊢ `(cl (not (= a b)) (= b a))` with premise `h : Eq α a b`
/// ⇒ `Eq.rec.{0,1} α a (fun x _ => Eq α x a) (Eq.refl α a) b h : Eq α b a`.
fn reconstruct_eq_symmetric(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // Conclusion clause: `(not (= a b)) (= b a)`.
    let [hyp, concl] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_symmetric".to_owned(),
            detail: format!("expected two literals, found {}", conclusion.len()),
        });
    };
    let (Some((a_t, b_t)), Some((c_t, d_t))) = (as_negated_eq(hyp), as_positive_eq(concl)) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_symmetric".to_owned(),
            detail: "expected `(cl (not (= a b)) (= b a))`".to_owned(),
        });
    };
    // The conclusion `(= b a)` must swap the hypothesis `(= a b)`.
    if a_t != d_t || b_t != c_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_symmetric".to_owned(),
            detail: "conclusion is not the swapped hypothesis".to_owned(),
        });
    }

    let a = ctx.alethe_term_to_expr(a_t)?;
    let b = ctx.alethe_term_to_expr(b_t)?;

    // The premise proof of `Eq α a b`. If an explicit premise term was threaded
    // in, use it; otherwise build the hypothesis as a fresh axiom `h : Eq α a b`
    // so the step is self-contained.
    let h = premise_or_axiom(ctx, premises, 0, a, b, "eq_symmetric")?;

    // motive := fun (x : α) (_ : Eq α a x) => Eq α x a.
    //   Under binders x, hx (innermost = BVar 0): in the body `Eq α x a`,
    //   x = BVar 1; in the hx domain `Eq α a x`, x = BVar 0.
    let motive = {
        let x1 = ctx.kernel.bvar(1);
        let eq_x_a = ctx.mk_eq(x1, a);
        let x0 = ctx.kernel.bvar(0);
        let eq_a_x = ctx.mk_eq(a, x0);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
        ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
    };
    // refl_case : motive a (Eq.refl α a) = Eq α a a, proved by `Eq.refl α a`.
    let refl_case = ctx.mk_eq_refl(a);
    // Eq.rec α a motive refl_case b h  :  motive b h  =  Eq α b a.
    let proof = ctx.mk_eq_rec_transport(a, motive, refl_case, b, h);

    let expected = ctx.mk_eq(b, a);
    check_against(ctx, "eq_symmetric", proof, expected)
}

/// Reconstruct the Alethe `symm` rule: one premise `h : Eq α a b`, conclusion
/// `(cl (= b a))`.
///
/// Unlike the clause-form `eq_symmetric` tautology (`(cl (not (= a b)) (= b a))`,
/// premise-free), `symm` is a *premise-consuming* step: it takes the prior unit
/// equality proof and concludes the flipped unit equality. The mathematical
/// content is identical, so the proof term is the same `Eq.rec` transport as
/// [`reconstruct_eq_symmetric`] (motive `fun x _ => Eq α x a`, refl-case
/// `Eq.refl α a`), built over the premise's operands.
///
/// Returns the swapped operands `(b, a)` alongside the kernel-checked proof so the
/// caller can record the resulting `(= b a)` unit.
///
/// # Errors
///
/// [`ReconstructError::MalformedStep`] when the conclusion is not a single positive
/// equality `(cl (= b a))` swapping the premise's `(= a b)`, and
/// [`ReconstructError::KernelRejected`] through the [`check_against`] gate.
pub(super) fn reconstruct_symm(
    ctx: &mut ReconstructCtx,
    premise_l: &AletheTerm,
    premise_r: &AletheTerm,
    premise_proof: ExprId,
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // Conclusion clause: the single positive `(= b a)`.
    let [concl] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: "symm".to_owned(),
            detail: format!("expected one literal, found {}", conclusion.len()),
        });
    };
    let Some((c_t, d_t)) = as_positive_eq(concl) else {
        return Err(ReconstructError::MalformedStep {
            rule: "symm".to_owned(),
            detail: "conclusion is not a positive equality `(= b a)`".to_owned(),
        });
    };
    // The conclusion `(= b a)` must swap the premise `(= a b)`.
    if c_t != premise_r || d_t != premise_l {
        return Err(ReconstructError::MalformedStep {
            rule: "symm".to_owned(),
            detail: "conclusion is not the swapped premise equality".to_owned(),
        });
    }

    let a = ctx.alethe_term_to_expr(premise_l)?;
    let b = ctx.alethe_term_to_expr(premise_r)?;

    // Same `Eq.rec` transport as `eq_symmetric`: motive `fun x _ => Eq α x a`,
    // refl-case `Eq.refl α a`, transported along `premise_proof : Eq α a b`.
    let motive = {
        let x1 = ctx.kernel.bvar(1);
        let eq_x_a = ctx.mk_eq(x1, a);
        let x0 = ctx.kernel.bvar(0);
        let eq_a_x = ctx.mk_eq(a, x0);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
        ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
    };
    let refl_case = ctx.mk_eq_refl(a);
    let proof = ctx.mk_eq_rec_transport(a, motive, refl_case, b, premise_proof);

    let expected = ctx.mk_eq(b, a);
    check_against(ctx, "symm", proof, expected)
}

/// `eq_transitive` ⊢ `(cl (not (= a b)) (not (= b c)) (= a c))` with premises
/// `h1 : Eq α a b`, `h2 : Eq α b c`
/// ⇒ `Eq.rec.{0,1} α b (fun x _ => Eq α a x) h1 c h2 : Eq α a c`.
fn reconstruct_eq_transitive(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // Conclusion clause: `(not (= a b)) (not (= b c)) (= a c)`.
    let [hyp1, hyp2, concl] = conclusion else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: format!(
                "this slice reconstructs a single 2-hypothesis chain; found {} literals",
                conclusion.len()
            ),
        });
    };
    let (Some((a_t, b_t)), Some((b2_t, c_t)), Some((ca_t, cc_t))) = (
        as_negated_eq(hyp1),
        as_negated_eq(hyp2),
        as_positive_eq(concl),
    ) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "expected `(cl (not (= a b)) (not (= b c)) (= a c))`".to_owned(),
        });
    };
    // The chain must connect: b_t == b2_t, and the conclusion endpoints a, c.
    if b_t != b2_t || a_t != ca_t || c_t != cc_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "chain links/conclusion endpoints do not match".to_owned(),
        });
    }

    let a = ctx.alethe_term_to_expr(a_t)?;
    let b = ctx.alethe_term_to_expr(b_t)?;
    let c = ctx.alethe_term_to_expr(c_t)?;

    let h1 = premise_or_axiom(ctx, premises, 0, a, b, "eq_transitive")?;
    let h2 = premise_or_axiom(ctx, premises, 1, b, c, "eq_transitive")?;

    // Transport `h1 : Eq α a b` along `h2 : Eq α b c` to `Eq α a c`, recursing on
    // `h2` (fixed left = b).
    // motive := fun (x : α) (_ : Eq α b x) => Eq α a x.
    //   Body `Eq α a x`: x = BVar 1; hx domain `Eq α b x`: x = BVar 0.
    let motive = {
        let x1 = ctx.kernel.bvar(1);
        let eq_a_x = ctx.mk_eq(a, x1);
        let x0 = ctx.kernel.bvar(0);
        let eq_b_x = ctx.mk_eq(b, x0);
        let anon = ctx.kernel.anon();
        let inner = ctx.kernel.lam(anon, eq_b_x, eq_a_x, BinderInfo::Default);
        ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
    };
    // refl_case : motive b (Eq.refl α b) = Eq α a b, proved by `h1`.
    let refl_case = h1;
    // Eq.rec α b motive h1 c h2  :  motive c h2  =  Eq α a c.
    let proof = ctx.mk_eq_rec_transport(b, motive, refl_case, c, h2);

    let expected = ctx.mk_eq(a, c);
    check_against(ctx, "eq_transitive", proof, expected)
}

/// Fetch the `idx`-th premise proof term, or — when no explicit premise was
/// supplied — synthesize a fresh hypothesis axiom `h : Eq α l r` so that a
/// self-contained Alethe `eq_*` step (whose hypotheses live inline in its
/// conclusion clause) is still reconstructible. The synthesized axiom is a
/// genuine kernel `Const` of the exact `Eq α l r` proposition, so the proof
/// term it feeds is well-typed.
fn premise_or_axiom(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    idx: usize,
    l: ExprId,
    r: ExprId,
    rule: &str,
) -> Result<ExprId, ReconstructError> {
    if let Some(&p) = premises.get(idx) {
        return Ok(p);
    }
    if !premises.is_empty() {
        // Some premises were supplied but not enough — that is a real mismatch.
        return Err(ReconstructError::MalformedStep {
            rule: rule.to_owned(),
            detail: format!("missing premise #{idx}"),
        });
    }
    // Premise-free Alethe step: model the inline hypothesis as an axiom.
    let eq_prop = ctx.mk_eq(l, r);
    let name = ctx.fresh_name("hyp");
    ctx.kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty: eq_prop,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: rule.to_owned(),
            detail: format!("hypothesis axiom did not admit: {e:?}"),
        })?;
    Ok(ctx.kernel.const_(name, vec![]))
}

/// Reconstruct an **n-ary** `eq_congruent` step into a kernel-checked proof term.
///
/// `eq_congruent` ⊢ `(cl (not (= a1 b1)) … (not (= an bn)) (= (f a1…an) (f b1…bn)))`
/// with premises `h_i : Eq α a_i b_i` proves the congruence of an arity-`n`
/// uninterpreted function `f`. Reconstruction transports one argument at a time:
/// starting from `Eq.refl α (f a…)`, each `h_i` drives an `Eq.rec` over the motive
/// `fun (x : α) (_ : Eq α a_i x) => Eq α (f a…) (f a1…a_{i-1} x b_{i+1}…)` (the
/// running accumulator is exactly that step's refl-case), ending at
/// `Eq α (f a1…an) (f b1…bn)`. The unary `f(a)=f(b)` shape is the `n = 1` case.
///
/// # Errors
///
/// Returns [`ReconstructError::MalformedStep`] for a clause whose literals are not
/// `(cl (not (= a1 b1)) … (not (= an bn)) (= (f a1…an) (f b1…bn)))` with matching
/// head/arity/arguments, and [`ReconstructError::UnsupportedRule`] when the
/// conclusion sides are not function applications; the kernel gate fires through
/// [`ReconstructError::KernelRejected`].
pub(super) fn reconstruct_eq_congruent(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // `(cl (not (= a1 b1)) … (not (= an bn)) (= (f a1…an) (f b1…bn)))`: a leading
    // negated equality per argument, then the positive application equality.
    let Some((concl, hyp_lits)) = conclusion.split_last() else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_congruent".to_owned(),
            detail: "empty conclusion clause".to_owned(),
        });
    };
    let Some((fa_t, fb_t)) = as_positive_eq(concl) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_congruent".to_owned(),
            detail: "last literal is not the positive `(= (f a…) (f b…))` conclusion".to_owned(),
        });
    };
    let (Some((f1, a_args)), Some((f2, b_args))) = (as_nary_app(fa_t), as_nary_app(fb_t)) else {
        return Err(ReconstructError::UnsupportedRule {
            rule: "eq_congruent (conclusion sides are not function applications)".to_owned(),
        });
    };
    if f1 != f2 || a_args.len() != b_args.len() || a_args.len() != hyp_lits.len() {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_congruent".to_owned(),
            detail: "head, arity, or hypothesis count mismatch".to_owned(),
        });
    }
    let arity = a_args.len();
    // Each hypothesis `i` is `(not (= a_i b_i))` for the i-th application argument.
    for (i, lit) in hyp_lits.iter().enumerate() {
        let Some((a_i, b_i)) = as_negated_eq(lit) else {
            return Err(ReconstructError::MalformedStep {
                rule: "eq_congruent".to_owned(),
                detail: "hypothesis is not a negated equality".to_owned(),
            });
        };
        if a_i != &a_args[i] || b_i != &b_args[i] {
            return Err(ReconstructError::MalformedStep {
                rule: "eq_congruent".to_owned(),
                detail: "hypothesis argument does not match the application argument".to_owned(),
            });
        }
    }

    let a_exprs: Vec<ExprId> = a_args
        .iter()
        .map(|t| ctx.alethe_term_to_expr(t))
        .collect::<Result<_, _>>()?;
    let b_exprs: Vec<ExprId> = b_args
        .iter()
        .map(|t| ctx.alethe_term_to_expr(t))
        .collect::<Result<_, _>>()?;
    let f_name = ctx.func_const(f1, arity);

    // Transport one argument at a time: `acc : Eq α (f a…) (f current)`, where
    // `current` starts as `a…` and position `i` is rewritten `a_i → b_i` each step.
    // The previous `acc` is exactly `motive_i a_i (refl)` (`current[i]` is still
    // `a_i`), so it serves as the Eq.rec refl-case.
    let fa = ctx.apply_func(f_name, &a_exprs);
    let mut acc = ctx.mk_eq_refl(fa);
    let mut current = a_exprs.clone();
    for i in 0..arity {
        // h_i : Eq α a_i b_i (explicit premise or self-contained inline axiom).
        let h = premise_or_axiom(ctx, premises, i, a_exprs[i], b_exprs[i], "eq_congruent")?;
        // motive := fun (x : α) (_ : Eq α a_i x) => Eq α (f a…) (f current[i := x]).
        //   Body: x = BVar 1; Eq-domain `Eq α a_i x`: x = BVar 0.
        let motive = {
            let x1 = ctx.kernel.bvar(1);
            let rhs = ctx.apply_func_with_hole(f_name, &current, i, x1);
            let eq_body = ctx.mk_eq(fa, rhs);
            let x0 = ctx.kernel.bvar(0);
            let eq_dom = ctx.mk_eq(a_exprs[i], x0);
            let anon = ctx.kernel.anon();
            let inner = ctx.kernel.lam(anon, eq_dom, eq_body, BinderInfo::Default);
            ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
        };
        // Eq.rec α a_i motive acc b_i h : Eq α (f a…) (f current[i := b_i]).
        acc = ctx.mk_eq_rec_transport(a_exprs[i], motive, acc, b_exprs[i], h);
        current[i] = b_exprs[i];
    }

    // acc : Eq α (f a1…an) (f b1…bn).
    let fb = ctx.apply_func(f_name, &b_exprs);
    let expected = ctx.mk_eq(fa, fb);
    check_against(ctx, "eq_congruent", acc, expected)
}

/// Reconstruct an **n-hypothesis** `eq_transitive` chain into a kernel-checked
/// proof term. The emitter folds a whole equality chain into a single
/// `eq_transitive` clause `(cl (not (= x0 x1)) … (not (= x_{k-1} xk)) (= x0 xk))`,
/// so the 2-hypothesis [`reconstruct_eq_transitive`] is not enough.
///
/// With ordered premise proofs `premises[i] : Eq α x_i x_{i+1}` (in clause order),
/// fold from the left: `acc : Eq α x0 x_{i}` is transported along
/// `premises[i] : Eq α x_i x_{i+1}` (motive `fun y _ => Eq α x0 y`) to
/// `Eq α x0 x_{i+1}`, ending at `Eq α x0 xk`.
///
/// # Errors
///
/// Returns [`ReconstructError::MalformedStep`] for a clause whose `k` leading
/// negated literals do not form a consecutive chain ending at the positive
/// conclusion `(= x0 xk)`, or a premise count that does not match the chain
/// length; [`ReconstructError::KernelRejected`] on the kernel gate.
pub(super) fn reconstruct_eq_transitive_n(
    ctx: &mut ReconstructCtx,
    premises: &[ExprId],
    conclusion: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    // Split into the leading negated chain links and the trailing positive concl.
    let Some((concl, links)) = conclusion.split_last() else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "empty conclusion clause".to_owned(),
        });
    };
    let Some((c0_t, ck_t)) = as_positive_eq(concl) else {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "last literal is not the positive `(= x0 xk)` conclusion".to_owned(),
        });
    };
    if links.is_empty() || premises.len() != links.len() {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: format!(
                "chain has {} links but {} premise proofs",
                links.len(),
                premises.len()
            ),
        });
    }

    // Collect the chain nodes `x0, x1, …, xk` from the consecutive negated links,
    // checking that each link starts where the previous ended.
    let mut nodes: Vec<&AletheTerm> = Vec::with_capacity(links.len() + 1);
    for (i, lit) in links.iter().enumerate() {
        let Some((l, r)) = as_negated_eq(lit) else {
            return Err(ReconstructError::MalformedStep {
                rule: "eq_transitive".to_owned(),
                detail: format!("link {i} is not a negated equality `(not (= _ _))`"),
            });
        };
        if i == 0 {
            nodes.push(l);
        } else if nodes[i] != l {
            return Err(ReconstructError::MalformedStep {
                rule: "eq_transitive".to_owned(),
                detail: format!("chain break: link {i} does not start at the previous endpoint"),
            });
        }
        nodes.push(r);
    }
    // Endpoints must match the conclusion `(= x0 xk)`.
    if nodes[0] != c0_t || nodes[nodes.len() - 1] != ck_t {
        return Err(ReconstructError::MalformedStep {
            rule: "eq_transitive".to_owned(),
            detail: "chain endpoints do not match the conclusion".to_owned(),
        });
    }

    // x0 is the fixed left operand of the accumulated equality.
    let x0 = ctx.alethe_term_to_expr(nodes[0])?;
    // acc : Eq α x0 x1  (the first premise proof).
    let mut acc = premises[0];
    // Fold links 1..k: transport acc : Eq α x0 x_i along premises[i] : Eq α x_i x_{i+1}.
    for i in 1..links.len() {
        let xi = ctx.alethe_term_to_expr(nodes[i])?;
        let xi1 = ctx.alethe_term_to_expr(nodes[i + 1])?;
        let h = premises[i];
        // motive := fun (y : α) (_ : Eq α x_i y) => Eq α x0 y.
        //   Body `Eq α x0 y`: y = BVar 1; hy domain `Eq α x_i y`: y = BVar 0.
        let motive = {
            let y1 = ctx.kernel.bvar(1);
            let eq_x0_y = ctx.mk_eq(x0, y1);
            let y0 = ctx.kernel.bvar(0);
            let eq_xi_y = ctx.mk_eq(xi, y0);
            let anon = ctx.kernel.anon();
            let inner = ctx.kernel.lam(anon, eq_xi_y, eq_x0_y, BinderInfo::Default);
            ctx.kernel.lam(anon, ctx.alpha, inner, BinderInfo::Default)
        };
        // Eq.rec α x_i motive acc x_{i+1} h : Eq α x0 x_{i+1}.
        acc = ctx.mk_eq_rec_transport(xi, motive, acc, xi1, h);
    }

    let ck = ctx.alethe_term_to_expr(ck_t)?;
    let expected = ctx.mk_eq(x0, ck);
    check_against(ctx, "eq_transitive", acc, expected)
}

/// Extract `(head, args)` of an n-ary application `(head arg…)` that is **not** an
/// equality (so a genuine function application, not `(= a b)` mis-parsed).
fn as_nary_app(term: &AletheTerm) -> Option<(&str, &[AletheTerm])> {
    match term {
        AletheTerm::App(head, args) if head != "=" && !args.is_empty() => {
            Some((head.as_str(), args.as_slice()))
        }
        _ => None,
    }
}
