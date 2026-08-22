//! Untrusted, bounded general producer: `Eq.refl`, and where that gets stuck,
//! a bounded structural induction over a naturally-shaped (zero/succ) binder
//! discovered from the kernel's own declarations plus a single congruence
//! rewrite driven by the induction hypothesis.
//!
//! This is deliberately target-agnostic: it never dispatches on a fact id, a
//! declaration name, or a hand-supplied proof plan. It discovers the
//! "zero/succ"-shaped inductive, its recursor, and the ambient `Eq`/`Eq.refl`/
//! `Eq.rec` primitives structurally from whatever kernel it is handed, and it
//! only ever emits a candidate that the SAME independent kernel then
//! re-type-checks through `Kernel::add_declaration`. Every budget below is an
//! explicit constant; exhausting one is a decline, never a hang.
//!
//! Known reach, measured against the six frozen `natural-factorial` goals
//! that reach the kernel and have their plain-`Eq.refl` candidate rejected
//! (see `docs/autogenesis/226-production-measurement-and-general-producer-plan.md`):
//! it closes `descFactorial n 1 = n`, `ascFactorial n 0 = 1`, and
//! `descFactorial n 0 = 1` (single induction, congrArg-with-hypothesis
//! bridges the `succ`-case). It declines `descFactorial n n = n!` (the
//! induction variable occurs in two positions at once — not a single-binder
//! shape), `n < k -> descFactorial n k = 0` (needs strong induction relating
//! two binders, not induction on one), and `ascFactorial 1 k = k!` /
//! `ascFactorial 0 k.succ = 0` (the needed step-case bridge is not a single
//! congruence — it also needs a commutativity-shaped normalization this
//! producer does not attempt). Every decline above is a real `Err`, checked
//! against the same kernel, never a silent skip.

use std::collections::BTreeSet;

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, NameId};

/// Maximum number of leading `Pi` binders this producer will peel (shared
/// budget across plain generalization and structural induction).
pub const MAX_BINDERS: usize = 8;

/// Maximum number of structural inductions this producer will perform while
/// building one candidate. Bounded so the search cannot recurse without limit
/// over nested zero/succ-shaped binders.
pub const MAX_INDUCTIONS: usize = 2;

/// First free-variable id this producer mints. Chosen far above anything an
/// import stream or the kernel's own `LocalContext` would use, so this
/// producer's free variables cannot collide with either.
const FVAR_BASE: u64 = 9_000_000;

/// One fully constructed candidate, plus the search shape that produced it —
/// reported so a caller can distinguish "closed by plain reflexivity" from
/// "closed by induction" without re-deriving it from the proof term.
#[derive(Debug)]
pub struct Candidate {
    pub proof: ExprId,
    pub binders_used: usize,
    pub inductions_used: usize,
}

/// Why the bounded search declined, tagged by stage so a caller can report a
/// precise, typed reason rather than a free-form string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclineReason {
    BinderBudgetExceeded,
    NotEqualityGoal,
    TerminalNotDefEqNoRewrite,
    RequiredDeclarationUnavailable(String),
    UnsupportedRecursorShape(String),
}

impl std::fmt::Display for DeclineReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BinderBudgetExceeded => {
                write!(f, "binder budget exceeded: maximum {MAX_BINDERS}")
            }
            Self::NotEqualityGoal => write!(f, "terminal goal is not an exact Eq application"),
            Self::TerminalNotDefEqNoRewrite => write!(
                f,
                "terminal goal is not definitionally equal and no applicable induction-hypothesis rewrite closed the gap"
            ),
            Self::RequiredDeclarationUnavailable(name) => {
                write!(
                    f,
                    "required declaration {name:?} occurs a number of times other than one"
                )
            }
            Self::UnsupportedRecursorShape(detail) => {
                write!(f, "unsupported recursor shape: {detail}")
            }
        }
    }
}

fn exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, DeclineReason> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(name, _)| {
            (kernel.display_name(*name).to_string() == rendered).then_some(*name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(DeclineReason::RequiredDeclarationUnavailable(
            rendered.to_owned(),
        )),
    }
}

fn app_spine(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}

/// Every `(prefix, argument)` split of `whole`'s application spine: for
/// `head a0 a1 … a_{n-1}`, the pair at index `i` is `(head a0 … a_{i-1},
/// a_i)`. Used to search for a congruence rewrite position anywhere along a
/// spine, not only at the outermost application.
fn spine_prefixes(kernel: &mut Kernel, whole: ExprId) -> Vec<(ExprId, ExprId)> {
    let (head, args) = app_spine(kernel, whole);
    let mut out = Vec::with_capacity(args.len());
    let mut prefix = head;
    for arg in args {
        out.push((prefix, arg));
        prefix = kernel.app(prefix, arg);
    }
    out
}

/// `fun (name : ty) => body`, abstracting the free variable `fv` in `body`.
/// A free function (not a `Search` method) since it only ever touches its
/// own arguments.
fn lam_fv(
    kernel: &mut Kernel,
    name: NameId,
    fv: u64,
    ty: ExprId,
    body: ExprId,
    info: BinderInfo,
) -> ExprId {
    let abstracted = kernel.abstract_fvars(body, &[fv]);
    kernel.lam(name, ty, abstracted, info)
}

/// `fun (name : ty) => partial_rec name`, where `partial_rec` was built at
/// this same scope using the free variable `major_fv` as the induction
/// target's stand-in; closes `major_fv` and applies the recursor to the
/// binder actually being introduced.
fn lam_fv_apply_major(
    kernel: &mut Kernel,
    name: NameId,
    major_fv: u64,
    ty: ExprId,
    info: BinderInfo,
    partial_rec: ExprId,
) -> ExprId {
    let major = kernel.fvar(major_fv);
    let applied = kernel.app(partial_rec, major);
    lam_fv(kernel, name, major_fv, ty, applied, info)
}

/// A parsed `Eq.{level} carrier lhs rhs` goal.
#[derive(Debug, Clone, Copy)]
struct EqGoal {
    level: LevelId,
    carrier: ExprId,
    lhs: ExprId,
    rhs: ExprId,
}

fn parse_eq_goal(kernel: &Kernel, eq_name: NameId, goal: ExprId) -> Result<EqGoal, DeclineReason> {
    let (head, arguments) = app_spine(kernel, goal);
    let ExprNode::Const(name, levels) = kernel.expr_node(head) else {
        return Err(DeclineReason::NotEqualityGoal);
    };
    if *name != eq_name || arguments.len() != 3 || levels.len() != 1 {
        return Err(DeclineReason::NotEqualityGoal);
    }
    Ok(EqGoal {
        level: levels[0],
        carrier: arguments[0],
        lhs: arguments[1],
        rhs: arguments[2],
    })
}

/// The ambient equality primitives, discovered by exact display name (never
/// hand-supplied), plus the exact universe-parameter arity each one needs —
/// checked rather than assumed, so a kernel with a different `Eq` shape
/// declines instead of building a term the kernel would reject anyway.
struct EqPrimitives {
    eq: NameId,
    eq_refl: NameId,
    eq_rec: NameId,
}

fn discover_eq_primitives(kernel: &Kernel) -> Result<EqPrimitives, DeclineReason> {
    let eq = exact_name(kernel, "Eq")?;
    let eq_refl = exact_name(kernel, "Eq.refl")?;
    let eq_rec = exact_name(kernel, "Eq.rec")?;
    let Some(Declaration::Recursor { uparams, .. }) = kernel.environment().get(eq_rec) else {
        return Err(DeclineReason::UnsupportedRecursorShape(
            "Eq.rec is not a Recursor declaration".to_owned(),
        ));
    };
    if uparams.len() != 2 {
        return Err(DeclineReason::UnsupportedRecursorShape(format!(
            "Eq.rec has {} universe parameters, expected 2",
            uparams.len()
        )));
    }
    Ok(EqPrimitives {
        eq,
        eq_refl,
        eq_rec,
    })
}

fn build_eq(
    kernel: &mut Kernel,
    eq: NameId,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let head = kernel.const_(eq, vec![level]);
    let with_carrier = kernel.app(head, carrier);
    let with_x = kernel.app(with_carrier, x);
    kernel.app(with_x, y)
}

fn build_eq_refl(
    kernel: &mut Kernel,
    eq_refl: NameId,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
) -> ExprId {
    let head = kernel.const_(eq_refl, vec![level]);
    let with_carrier = kernel.app(head, carrier);
    kernel.app(with_carrier, x)
}

/// A zero/succ-shaped inductive: exactly two constructors, no parameters, no
/// indices — one nullary ("zero"), one with exactly one field recursive on
/// the family itself ("succ") — plus its generated recursor, discovered by
/// inspecting `Kernel::environment()`, never by name.
struct NatShape {
    zero_ctor: NameId,
    succ_ctor: NameId,
    rec_name: NameId,
}

fn ctor_is_zero_shaped(kernel: &Kernel, ctor: NameId) -> bool {
    matches!(
        kernel.environment().get(ctor),
        Some(Declaration::Constructor { num_fields: 0, .. })
    )
}

fn ctor_is_succ_shaped(kernel: &Kernel, ctor: NameId, family: NameId) -> bool {
    let Some(Declaration::Constructor {
        ty, num_fields: 1, ..
    }) = kernel.environment().get(ctor)
    else {
        return false;
    };
    let ExprNode::Pi(_, field_ty, body, _) = kernel.expr_node(*ty) else {
        return false;
    };
    let field_is_family =
        matches!(kernel.expr_node(*field_ty), ExprNode::Const(n, _) if *n == family);
    let result_is_family = matches!(kernel.expr_node(*body), ExprNode::Const(n, _) if *n == family);
    field_is_family && result_is_family
}

fn detect_nat_shape(kernel: &Kernel, family: NameId) -> Option<NatShape> {
    let Some(Declaration::Inductive {
        num_params,
        num_indices,
        ctor_names,
        ..
    }) = kernel.environment().get(family)
    else {
        return None;
    };
    if *num_params != 0 || *num_indices != 0 || ctor_names.len() != 2 {
        return None;
    }
    let (c0, c1) = (ctor_names[0], ctor_names[1]);
    let (zero_ctor, succ_ctor) =
        if ctor_is_zero_shaped(kernel, c0) && ctor_is_succ_shaped(kernel, c1, family) {
            (c0, c1)
        } else if ctor_is_zero_shaped(kernel, c1) && ctor_is_succ_shaped(kernel, c0, family) {
            (c1, c0)
        } else {
            return None;
        };
    for (name, decl) in kernel.environment().iter() {
        let Declaration::Recursor {
            rec_rules,
            num_motives,
            num_minors,
            num_params: rp,
            num_indices: ri,
            uparams,
            ..
        } = decl
        else {
            continue;
        };
        if *rp != 0 || *ri != 0 || *num_motives != 1 || *num_minors != 2 || uparams.len() != 1 {
            continue;
        }
        let rule_ctors: BTreeSet<NameId> = rec_rules.iter().map(|rule| rule.ctor_name).collect();
        if rule_ctors == BTreeSet::from([zero_ctor, succ_ctor]) {
            return Some(NatShape {
                zero_ctor,
                succ_ctor,
                rec_name: *name,
            });
        }
    }
    None
}

/// A live induction hypothesis available while closing a subgoal: a proof of
/// `stmt`. `stmt` may still carry leading `Pi`s of its own (when further
/// binders follow the induction variable in the original goal) — it is
/// peeled in lockstep with the goal by [`instantiate_hypothesis`] as
/// `Search::attempt` generalizes each further binder, and parsed into an
/// [`EqGoal`] only once [`Search::close_terminal`] actually needs it.
#[derive(Debug, Clone, Copy)]
struct Hypothesis {
    proof: ExprId,
    stmt: ExprId,
}

/// Peel one `Pi` off `hypothesis.stmt`, applying its proof to `x` to match the
/// goal's own generalization of the same binder. Returns `None` (dropping the
/// hypothesis rather than failing the search) if `stmt` is not a `Pi` here —
/// a genuine shape mismatch between the induction hypothesis and the goal,
/// which should cost this one rewrite opportunity, not the whole candidate.
fn instantiate_hypothesis(
    kernel: &mut Kernel,
    hypothesis: Hypothesis,
    x: ExprId,
) -> Option<Hypothesis> {
    let ExprNode::Pi(_, _, body, _) = kernel.expr_node(hypothesis.stmt).clone() else {
        return None;
    };
    let stmt = kernel.instantiate(body, &[x]);
    let proof = kernel.app(hypothesis.proof, x);
    Some(Hypothesis { proof, stmt })
}

/// A `Pi` binder mid-descent, bundled to keep `try_induction`'s arity small.
#[derive(Debug, Clone, Copy)]
struct Binder {
    name: NameId,
    ty: ExprId,
    info: BinderInfo,
    body: ExprId,
}

struct Search {
    eqp_eq: NameId,
    eqp_refl: NameId,
    eqp_rec: NameId,
    next_fvar: u64,
    binders_left: usize,
    inductions_left: usize,
    binders_used: usize,
    inductions_used: usize,
}

impl Search {
    fn fresh_fvar(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    /// Try to close `goal` (already peeled of every leading binder) via
    /// `Eq.refl`, or via one congruence rewrite driven by `hypothesis`.
    fn close_terminal(
        &mut self,
        kernel: &mut Kernel,
        goal: EqGoal,
        hypothesis: Option<Hypothesis>,
    ) -> Result<ExprId, DeclineReason> {
        if kernel.def_eq(goal.lhs, goal.rhs) {
            return Ok(build_eq_refl(
                kernel,
                self.eqp_refl,
                goal.level,
                goal.carrier,
                goal.lhs,
            ));
        }
        // The hypothesis is only usable once its (possibly still-Pi-headed)
        // statement has been peeled down to the same `Eq` shape as `goal` —
        // by the same number of `Search::attempt` generalization steps. A
        // hypothesis that is present but does not (yet, or ever) parse this
        // way is simply unavailable for this rewrite, not a hard error.
        let Some((hyp_proof, hyp_goal)) = hypothesis.and_then(|hyp| {
            parse_eq_goal(kernel, self.eqp_eq, hyp.stmt)
                .ok()
                .map(|g| (hyp.proof, g))
        }) else {
            return Err(DeclineReason::TerminalNotDefEqNoRewrite);
        };
        // Try deriving the rewrite "wrap" from the (whnf-reduced) RHS: some
        // application prefix `f` of `rhs` applied to an argument defeq to the
        // hypothesis's own right-hand side, with `f(hyp_goal.lhs)` defeq the
        // goal's left-hand side. Every split of the application spine is
        // tried, not just the outermost one, because the matching argument
        // position can sit anywhere along a `brecOn`/course-of-values-compiled
        // spine.
        let rhs_whnf = kernel.whnf(goal.rhs);
        for (f, arg) in spine_prefixes(kernel, rhs_whnf).into_iter().rev() {
            if kernel.def_eq(arg, hyp_goal.rhs) {
                let candidate_lhs = kernel.app(f, hyp_goal.lhs);
                if kernel.def_eq(candidate_lhs, goal.lhs) {
                    return Ok(self.build_congr(kernel, f, hyp_proof, hyp_goal, goal));
                }
            }
        }
        // Symmetric attempt: derive the wrap from the (whnf-reduced) LHS.
        let lhs_whnf = kernel.whnf(goal.lhs);
        for (f, arg) in spine_prefixes(kernel, lhs_whnf).into_iter().rev() {
            if kernel.def_eq(arg, hyp_goal.lhs) {
                let candidate_rhs = kernel.app(f, hyp_goal.rhs);
                if kernel.def_eq(candidate_rhs, goal.rhs) {
                    return Ok(self.build_congr(kernel, f, hyp_proof, hyp_goal, goal));
                }
            }
        }
        Err(DeclineReason::TerminalNotDefEqNoRewrite)
    }

    /// `congrArg f hyp : Eq goal.carrier (f hyp.lhs) (f hyp.rhs)`, built
    /// directly from the kernel's generated `Eq.rec` (never a hand-written
    /// `congrArg` theorem — none exists in an isolated statement-import
    /// kernel), so its type is checked against `goal` only when the caller
    /// declares the surrounding theorem.
    fn build_congr(
        &mut self,
        kernel: &mut Kernel,
        f: ExprId,
        hyp_proof: ExprId,
        hyp_goal: EqGoal,
        goal: EqGoal,
    ) -> ExprId {
        let anon = kernel.anon();
        let fa = kernel.app(f, hyp_goal.lhs);
        // motive := fun (x : hyp_goal.carrier) (_ : Eq hyp_goal.level hyp_goal.carrier hyp_goal.lhs x) =>
        //             Eq goal.level goal.carrier fa (f x)
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let fx = kernel.app(f, x);
        let concl = build_eq(kernel, self.eqp_eq, goal.level, goal.carrier, fa, fx);
        let hyp_ty = build_eq(
            kernel,
            self.eqp_eq,
            hyp_goal.level,
            hyp_goal.carrier,
            hyp_goal.lhs,
            x,
        );
        let anon_hyp = kernel.anon();
        let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
        let motive = lam_fv(
            kernel,
            anon,
            x_fv,
            hyp_goal.carrier,
            inner,
            BinderInfo::Default,
        );
        let refl_case = build_eq_refl(kernel, self.eqp_refl, goal.level, goal.carrier, fa);
        let z = kernel.level_zero();
        let rec = kernel.const_(self.eqp_rec, vec![z, hyp_goal.level]);
        let with_carrier = kernel.app(rec, hyp_goal.carrier);
        let with_a = kernel.app(with_carrier, hyp_goal.lhs);
        let with_motive = kernel.app(with_a, motive);
        let with_minor = kernel.app(with_motive, refl_case);
        let with_b = kernel.app(with_minor, hyp_goal.rhs);
        kernel.app(with_b, hyp_proof)
    }

    /// Structural induction on a zero/succ-shaped binder: build
    /// `T.rec {motive} case_zero case_succ` and apply it directly to the
    /// binder's own bound value, without leaving this binder's `Pi`.
    fn try_induction(
        &mut self,
        kernel: &mut Kernel,
        shape: &NatShape,
        binder: Binder,
        eqp: &EqPrimitives,
        hypothesis: Option<Hypothesis>,
    ) -> Result<ExprId, DeclineReason> {
        let Binder {
            name: binder_name,
            ty: binder_ty,
            info: binder_info,
            body,
        } = binder;
        let anon = kernel.anon();
        let zero_e = kernel.const_(shape.zero_ctor, vec![]);
        let succ_e = kernel.const_(shape.succ_ctor, vec![]);

        // The induction target's own free variable, used only to compute
        // subgoals; the final motive/case terms are re-closed via
        // `abstract_fvars` before this function returns.
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let prop_at_x = kernel.instantiate(body, &[x]);
        let motive = lam_fv(kernel, anon, x_fv, binder_ty, prop_at_x, binder_info);

        // Base case: prove the goal at `zero`. Recursing through `attempt`
        // (rather than assuming `body` is already a bare `Eq`) lets this
        // close goals where further binders — plain hypotheses, or another
        // zero/succ-shaped variable — follow the induction variable.
        let base_goal_expr = kernel.instantiate(body, &[zero_e]);
        let case_zero = self.attempt(kernel, base_goal_expr, eqp, hypothesis)?;

        // Step case: fresh predecessor + induction hypothesis, prove the goal
        // at `succ pred`. The hypothesis carries `body` instantiated at
        // `pred` verbatim — still possibly `Pi`-headed — and is peeled in
        // lockstep with the goal by `instantiate_hypothesis` as `attempt`
        // generalizes any further binders below.
        let pred_fv = self.fresh_fvar();
        let pred = kernel.fvar(pred_fv);
        let ih_fv = self.fresh_fvar();
        let ih = kernel.fvar(ih_fv);
        let pred_goal_expr = kernel.instantiate(body, &[pred]);
        let succ_pred = kernel.app(succ_e, pred);
        let step_goal_expr = kernel.instantiate(body, &[succ_pred]);
        let step_ih = Hypothesis {
            proof: ih,
            stmt: pred_goal_expr,
        };
        let step_proof = self.attempt(kernel, step_goal_expr, eqp, Some(step_ih))?;
        let step_body = lam_fv(
            kernel,
            anon,
            ih_fv,
            pred_goal_expr,
            step_proof,
            BinderInfo::Default,
        );
        let case_succ = lam_fv(
            kernel,
            anon,
            pred_fv,
            binder_ty,
            step_body,
            BinderInfo::Default,
        );

        let z = kernel.level_zero();
        let rec = kernel.const_(shape.rec_name, vec![z]);
        let with_motive = kernel.app(rec, motive);
        let with_zero = kernel.app(with_motive, case_zero);
        let with_succ = kernel.app(with_zero, case_succ);

        // Apply this partial recursor application to the CURRENT binder's own
        // value, then wrap in exactly the caller's `Pi(binder_name, ...)`
        // shape (`with_succ`/`motive`/`case_zero`/`case_succ` all sit at the
        // same scope depth as `body` itself, so closing them into the current
        // binder is the ordinary fvar/`abstract_fvars` pattern, never manual
        // de Bruijn arithmetic).
        Ok(lam_fv_apply_major(
            kernel,
            binder_name,
            x_fv,
            binder_ty,
            binder_info,
            with_succ,
        ))
    }

    fn attempt(
        &mut self,
        kernel: &mut Kernel,
        goal: ExprId,
        eqp: &EqPrimitives,
        hypothesis: Option<Hypothesis>,
    ) -> Result<ExprId, DeclineReason> {
        if let ExprNode::Pi(name, ty, body, info) = kernel.expr_node(goal) {
            let (name, ty, body, info) = (*name, *ty, *body, *info);
            if self.binders_left == 0 {
                return Err(DeclineReason::BinderBudgetExceeded);
            }
            self.binders_left -= 1;
            self.binders_used += 1;

            if self.inductions_left > 0 {
                let ty_whnf = kernel.whnf(ty);
                let family = match kernel.expr_node(ty_whnf) {
                    ExprNode::Const(n, _) => Some(*n),
                    _ => None,
                };
                if let Some(family) = family
                    && let Some(shape) = detect_nat_shape(kernel, family)
                {
                    self.inductions_left -= 1;
                    self.inductions_used += 1;
                    let binder = Binder {
                        name,
                        ty,
                        info,
                        body,
                    };
                    if let Ok(proof) = self.try_induction(kernel, &shape, binder, eqp, hypothesis) {
                        return Ok(proof);
                    }
                    self.inductions_left += 1;
                    self.inductions_used -= 1;
                }
            }

            // Plain generalization: introduce a fresh opaque variable and
            // keep going. A live hypothesis is peeled in lockstep — it was
            // built over the SAME remaining binder structure as `body`, so
            // one more generalization here means one more application there
            // (or the hypothesis quietly stops being usable, which is a lost
            // rewrite opportunity, never a hard failure).
            let fv = self.fresh_fvar();
            let x = kernel.fvar(fv);
            let sub_goal = kernel.instantiate(body, &[x]);
            let sub_hypothesis = hypothesis.and_then(|hyp| instantiate_hypothesis(kernel, hyp, x));
            let sub_proof = self.attempt(kernel, sub_goal, eqp, sub_hypothesis)?;
            return Ok(lam_fv(kernel, name, fv, ty, sub_proof, info));
        }
        let parsed = parse_eq_goal(kernel, eqp.eq, goal)?;
        self.close_terminal(kernel, parsed, hypothesis)
    }
}

/// Attempt `Eq.refl`, and where that is stuck, a bounded structural induction
/// over a zero/succ-shaped binder plus one congruence rewrite driven by the
/// induction hypothesis. Never dispatches on the target's name or fact id;
/// every structural fact it uses (the equality primitives, the inductive
/// shape, the recursor) is discovered from `kernel`'s own declarations.
pub fn propose_bounded_induction(
    kernel: &mut Kernel,
    goal: ExprId,
) -> Result<Candidate, DeclineReason> {
    let eqp = discover_eq_primitives(kernel)?;
    let mut search = Search {
        eqp_eq: eqp.eq,
        eqp_refl: eqp.eq_refl,
        eqp_rec: eqp.eq_rec,
        next_fvar: FVAR_BASE,
        binders_left: MAX_BINDERS,
        inductions_left: MAX_INDUCTIONS,
        binders_used: 0,
        inductions_used: 0,
    };
    let proof = search.attempt(kernel, goal, &eqp, None)?;
    Ok(Candidate {
        proof,
        binders_used: search.binders_used,
        inductions_used: search.inductions_used,
    })
}
