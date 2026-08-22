//! Untrusted, bounded general producer: `Eq.refl`, and where that gets stuck,
//! a bounded structural induction over a naturally-shaped (zero/succ) binder,
//! plus one or more congruence rewrites driven by the induction hypothesis —
//! including, where a single rewrite is not enough, a self-contained
//! auxiliary arithmetic lemma discovered and proved by the SAME mechanism and
//! spliced in with `Eq.trans`.
//!
//! This is deliberately target-agnostic: it never dispatches on a fact id, a
//! declaration name, or a hand-supplied proof plan. It discovers the
//! "zero/succ"-shaped inductive, its recursor, and the ambient `Eq`/`Eq.refl`/
//! `Eq.rec` primitives structurally from whatever kernel it is handed, and it
//! only ever emits a candidate that the SAME independent kernel then
//! re-type-checks through `Kernel::add_declaration`. Every budget below is an
//! explicit constant; exhausting one is a decline, never a hang.
//!
//! Known reach, measured against the seven frozen `natural-factorial` goals
//! that reach the kernel and have their plain-`Eq.refl` candidate rejected
//! (see `docs/autogenesis/226-production-measurement-and-general-producer-plan.md`
//! and `docs/autogenesis/232-first-general-producer-result.md`): it closes
//! `descFactorial n 1 = n`, `ascFactorial n 0 = 1`, and `descFactorial n 0 =
//! 1` (single induction, one congrArg-with-hypothesis rewrite bridges the
//! `succ`-case); and, via the residual-lemma extension
//! ([`Search::try_residual_lemma`]), `ascFactorial 0 k.succ = 0` (the
//! step-case's second factor multiplies out to `0` regardless of the first,
//! closed by [`kabstract_occurrences`] finding the induction hypothesis
//! occurrence behind a `brecOn`/`below` structure *projection* — a shape
//! spine-argument matching alone could not see into) and `ascFactorial 1 k =
//! k!` (the step-case bridge needs the auxiliary identity `1 + n = n.succ`,
//! proved as its own nested, budget-sharing induction and composed with the
//! primary congruence via `Eq.trans`). It declines `descFactorial n n = n!`
//! (the induction variable occurs in two positions at once — a genuinely
//! diagonal recursion where the induction hypothesis's shape does not
//! directly relate `descFactorial (n+1) n` back to `descFactorial n n`,
//! needing more than a rewrite chain) and `n < k -> descFactorial n k = 0`
//! (needs a hypothesis-driven case split this producer does not attempt: the
//! base case `n < 0` is vacuous, and closing it needs eliminating an
//! impossible `Nat.le` proof via ITS OWN indexed recursor — a capability
//! entirely absent here, distinct from the zero/succ structural induction
//! this producer performs on the GOAL's own binders). Every decline above is
//! a real `Err`, checked against the same kernel, never a silent skip.

use std::collections::BTreeSet;

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, NameId};

/// Maximum number of leading `Pi` binders this producer will peel (shared
/// budget across plain generalization and structural induction).
pub const MAX_BINDERS: usize = 8;

/// Maximum number of structural inductions this producer will perform while
/// building one candidate. Bounded so the search cannot recurse without limit
/// over nested zero/succ-shaped binders.
pub const MAX_INDUCTIONS: usize = 2;

/// Maximum number of residual auxiliary-lemma attempts
/// ([`Search::try_residual_lemma`]) one derivation may make in total,
/// decremented on every attempt regardless of outcome. A congruence rewrite
/// whose final check fails only up to an arithmetic identity between two
/// zero/succ-shaped terms (e.g. `1 + n = n.succ`, needed when a course-of-
/// values-compiled operator's recursion argument is itself a sum rather than
/// a bare variable) is generalized back into its own standalone `Pi` goal
/// and proved via a nested, budget-sharing call to [`Search::attempt`] —
/// this bounds how many such side quests one derivation may spawn, so the
/// capability cannot turn a single decline into unbounded extra search.
pub const MAX_RESIDUAL_LEMMAS: usize = 4;

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

/// Maximum number of sub-expression nodes [`kabstract_occurrences`] will
/// visit while searching for occurrences of a hypothesis side inside a goal
/// side. Bounded so a pathologically large `brecOn`/`below` unfolding cannot
/// hang the search; exhausting it makes the search report "not found",
/// never a panic or an unbounded loop.
const MAX_KABSTRACT_NODES: usize = 4_096;

/// Maximum number of sub-expression nodes [`collect_fvars`] will visit while
/// finding which free variables occur in a residual gap's two sides. Same
/// role as [`MAX_KABSTRACT_NODES`] — bounds a recursive term walk so it
/// reports an (under-approximate, never wrong) partial result instead of
/// hanging on a pathologically large term.
const MAX_FVAR_COLLECT_NODES: usize = 4_096;

/// Maximum recursion depth [`find_diff`] will descend while narrowing a
/// residual gap to its actual point of difference. Bounded the same way as
/// [`MAX_KABSTRACT_NODES`]/[`MAX_FVAR_COLLECT_NODES`]: exhausting it makes
/// the search fall back to the coarser, whole-term pair rather than hang or
/// panic.
const MAX_DIFF_NODES: usize = 256;

/// Find the point where `a` and `b` — known not to be definitionally equal —
/// actually diverge, by descending through matching `App` spines wherever
/// the function part still matches exactly (so the shared context is kept
/// intact) but the trailing argument does not. Returns `None` only if `a`/`b`
/// turn out definitionally equal at some recursion step (never at the top,
/// since the caller already knows they are not); returns `Some((a, b))`
/// unchanged when no further descent is possible, which is the correct,
/// maximally-conservative answer for "the whole pair is the diff" — this
/// function only ever narrows, never fabricates a diff that does not truly
/// separate the two sides.
///
/// Deliberately does **not** descend into the function position when only
/// the *trailing* arguments happen to coincide (the symmetric case): two
/// differently-curried applications can share a final argument by
/// coincidence (e.g. `n.succ` vs a 6-argument `HAdd.hAdd … 1 n` both ending
/// in the same `n`) while the "remaining" function-position comparison
/// after stripping it is a bare constant against a partial application —
/// not a meaningful pointwise identity, and one this producer has no
/// business trying to prove (it would need function extensionality, not
/// induction). Keeping only the shared-context direction means every
/// diff this returns is a genuine same-shape divergence.
fn find_diff(
    kernel: &mut Kernel,
    a: ExprId,
    b: ExprId,
    budget: &mut usize,
) -> Option<(ExprId, ExprId)> {
    if *budget == 0 {
        return Some((a, b));
    }
    *budget -= 1;
    if kernel.def_eq(a, b) {
        return None;
    }
    if let (ExprNode::App(f1, x1), ExprNode::App(f2, x2)) =
        (kernel.expr_node(a).clone(), kernel.expr_node(b).clone())
        && kernel.def_eq(f1, f2)
    {
        return find_diff(kernel, x1, x2, budget).or(Some((a, b)));
    }
    Some((a, b))
}

/// Collect every free-variable id occurring anywhere in `e` (including under
/// `Lam`/`Pi`/`Let`, since — unlike [`kabstract_occurrences`] — there is no
/// binder-crossing hazard in merely recording that an id occurs) into `out`.
/// Bounded by `budget`; exhausting it stops the walk early rather than
/// hanging, which can only under-report occurrences, never fabricate one —
/// a caller that then fails to find a variable's type simply declines.
fn collect_fvars(
    kernel: &Kernel,
    e: ExprId,
    out: &mut std::collections::BTreeSet<u64>,
    budget: &mut usize,
) {
    if *budget == 0 {
        return;
    }
    *budget -= 1;
    match kernel.expr_node(e) {
        ExprNode::FVar(id) => {
            out.insert(*id);
        }
        ExprNode::App(f, a) => {
            let (f, a) = (*f, *a);
            collect_fvars(kernel, f, out, budget);
            collect_fvars(kernel, a, out, budget);
        }
        ExprNode::Proj(_, _, inner) => {
            let inner = *inner;
            collect_fvars(kernel, inner, out, budget);
        }
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
            let (ty, body) = (*ty, *body);
            collect_fvars(kernel, ty, out, budget);
            collect_fvars(kernel, body, out, budget);
        }
        ExprNode::Let(_, ty, val, body) => {
            let (ty, val, body) = (*ty, *val, *body);
            collect_fvars(kernel, ty, out, budget);
            collect_fvars(kernel, val, out, budget);
            collect_fvars(kernel, body, out, budget);
        }
        _ => {}
    }
}

/// Abstract every occurrence of `needle` inside `haystack` (compared up to
/// definitional equality, so it finds occurrences regardless of how they are
/// currently folded/unfolded) into the given `placeholder` free variable,
/// recursing through `App`, `Proj`, and a binder's own type annotation —
/// never into a `Lam`/`Pi`/`Let` *body*, since those are expressed with de
/// Bruijn indices relative to a binder this function does not open, and a
/// closed `needle` can never actually occur there matched against `whole`'s
/// own bound variables. Returns the rewritten term and whether any
/// occurrence was found; finding none returns `haystack` unchanged, not an
/// error — the caller decides what a lack of match means.
///
/// This is the same operation Lean's own `rw` tactic calls `kabstract`: the
/// generalization from the previous single-spine-position search this
/// producer used, needed because a course-of-values (`brecOn`/`below`)
/// compiled recursive definition routes a nested recursive call through a
/// structure *projection* before it reaches an argument slot of the outer
/// operator — a shape `App`-only spine peeling cannot see into.
fn kabstract_occurrences(
    kernel: &mut Kernel,
    haystack: ExprId,
    needle: ExprId,
    placeholder: ExprId,
    budget: &mut usize,
) -> (ExprId, bool) {
    if *budget == 0 {
        return (haystack, false);
    }
    *budget -= 1;
    if kernel.def_eq(haystack, needle) {
        return (placeholder, true);
    }
    match kernel.expr_node(haystack).clone() {
        ExprNode::App(f, a) => {
            let (f2, found_f) = kabstract_occurrences(kernel, f, needle, placeholder, budget);
            let (a2, found_a) = kabstract_occurrences(kernel, a, needle, placeholder, budget);
            if found_f || found_a {
                (kernel.app(f2, a2), true)
            } else {
                (haystack, false)
            }
        }
        ExprNode::Proj(type_name, field_index, inner) => {
            let (inner2, found) = kabstract_occurrences(kernel, inner, needle, placeholder, budget);
            if found {
                (kernel.proj(type_name, field_index, inner2), true)
            } else {
                (haystack, false)
            }
        }
        ExprNode::Lam(name, ty, body, info) => {
            let (ty2, found) = kabstract_occurrences(kernel, ty, needle, placeholder, budget);
            if found {
                (kernel.lam(name, ty2, body, info), true)
            } else {
                (haystack, false)
            }
        }
        ExprNode::Pi(name, ty, body, info) => {
            let (ty2, found) = kabstract_occurrences(kernel, ty, needle, placeholder, budget);
            if found {
                (kernel.pi(name, ty2, body, info), true)
            } else {
                (haystack, false)
            }
        }
        ExprNode::Let(name, ty, val, body) => {
            let (ty2, found_ty) = kabstract_occurrences(kernel, ty, needle, placeholder, budget);
            let (val2, found_val) = kabstract_occurrences(kernel, val, needle, placeholder, budget);
            if found_ty || found_val {
                (kernel.let_(name, ty2, val2, body), true)
            } else {
                (haystack, false)
            }
        }
        _ => (haystack, false),
    }
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
    /// The type recorded for every free variable minted through
    /// [`Search::fresh_fvar_typed`] — every induction target, induction
    /// predecessor, and plain-generalized binder the search has introduced
    /// so far. Consulted only by the residual-lemma path
    /// ([`Search::try_residual_lemma`]): to generalize a stuck subterm back
    /// into a standalone universally-quantified auxiliary goal, the search
    /// needs the ORIGINAL binder type for each free variable occurring in
    /// it, not just the variable's numeric id.
    fvar_types: std::collections::BTreeMap<u64, ExprId>,
    /// How many residual auxiliary-lemma attempts
    /// ([`Search::try_residual_lemma`]) this whole derivation may still make,
    /// decremented on every attempt regardless of outcome. Bounds the total
    /// extra search this capability can spend, independent of — and on top
    /// of — [`MAX_BINDERS`]/[`MAX_INDUCTIONS`], which the residual attempt
    /// also shares and is bound by.
    residual_budget: usize,
}

impl Search {
    fn fresh_fvar(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    /// [`Search::fresh_fvar`], additionally recording `ty` as that
    /// variable's type for the residual-lemma generalizer.
    fn fresh_fvar_typed(&mut self, ty: ExprId) -> u64 {
        let fv = self.fresh_fvar();
        self.fvar_types.insert(fv, ty);
        fv
    }

    /// Try to close `goal` (already peeled of every leading binder) via
    /// `Eq.refl`, or via one congruence rewrite driven by `hypothesis`.
    fn close_terminal(
        &mut self,
        kernel: &mut Kernel,
        goal: EqGoal,
        hypothesis: Option<Hypothesis>,
    ) -> Result<ExprId, DeclineReason> {
        if std::env::var("BIS_DEBUG").is_ok() {
            eprintln!(
                "close_terminal: lhs={} rhs={} hyp={}",
                kernel.render_lean(goal.lhs),
                kernel.render_lean(goal.rhs),
                hypothesis.map_or_else(|| "<none>".to_string(), |h| kernel.render_lean(h.stmt))
            );
        }
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
        // Try deriving the rewrite "wrap" `f` by abstracting every occurrence
        // of the hypothesis's RHS anywhere inside the (whnf-reduced) goal RHS
        // — not only at a spine-argument position. A course-of-values
        // (`brecOn`/`below`) compiled definition routes a recursive call
        // through a structure *projection* (`(below-pack).1`) before it ever
        // reaches an argument slot of the outer operator, so restricting the
        // search to `App` spine positions missed exactly the shape a second
        // arithmetic operator (e.g. multiplication consuming a `descFactorial`
        // recursive call as its own recursion scrutinee) produces. Searching
        // every subterm reachable through `App`/`Proj`/a binder's own type
        // finds the occurrence regardless of how deep the projection nesting
        // goes, while still building exactly one `congrArg`-shaped rewrite —
        // never more than the single hypothesis already in hand.
        let debug = std::env::var("BIS_DEBUG").is_ok();
        let rhs_whnf = kernel.whnf(goal.rhs);
        if debug {
            eprintln!("  rhs_whnf={}", kernel.render_lean(rhs_whnf));
        }
        if let Some(proof) = self.try_congr_rewrite(
            kernel,
            rhs_whnf,
            hyp_goal.rhs,
            hyp_goal.lhs,
            goal.lhs,
            true,
            hyp_proof,
            hyp_goal,
            goal,
            debug,
        ) {
            return Ok(proof);
        }
        // Symmetric attempt: derive the wrap from the (whnf-reduced) LHS.
        let lhs_whnf = kernel.whnf(goal.lhs);
        if debug {
            eprintln!("  lhs_whnf={}", kernel.render_lean(lhs_whnf));
        }
        if let Some(proof) = self.try_congr_rewrite(
            kernel,
            lhs_whnf,
            hyp_goal.lhs,
            hyp_goal.rhs,
            goal.rhs,
            false,
            hyp_proof,
            hyp_goal,
            goal,
            debug,
        ) {
            return Ok(proof);
        }
        Err(DeclineReason::TerminalNotDefEqNoRewrite)
    }

    /// Abstract every occurrence of `needle` inside `haystack` into a fresh
    /// binder, giving a candidate wrap `f`; if any occurrence was found and
    /// `f(other_side)` is definitionally equal to `expected`, build and
    /// return the `congrArg`-shaped proof. Returns `None` (never a hard
    /// error) when no occurrence exists or the resulting wrap does not close
    /// the gap — the caller tries the symmetric direction next.
    #[allow(clippy::too_many_arguments)]
    fn try_congr_rewrite(
        &mut self,
        kernel: &mut Kernel,
        haystack: ExprId,
        needle: ExprId,
        other_side: ExprId,
        expected: ExprId,
        other_is_hyp_lhs: bool,
        hyp_proof: ExprId,
        hyp_goal: EqGoal,
        goal: EqGoal,
        debug: bool,
    ) -> Option<ExprId> {
        let placeholder_fv = self.fresh_fvar();
        let placeholder = kernel.fvar(placeholder_fv);
        let mut budget = MAX_KABSTRACT_NODES;
        let (replaced, found) =
            kabstract_occurrences(kernel, haystack, needle, placeholder, &mut budget);
        if !found {
            if debug {
                eprintln!(
                    "  [kabstract] no occurrence of {} in {}",
                    kernel.render_lean(needle),
                    kernel.render_lean(haystack)
                );
            }
            return None;
        }
        let anon = kernel.anon();
        let abstracted = kernel.abstract_fvars(replaced, &[placeholder_fv]);
        let f = kernel.lam(anon, hyp_goal.carrier, abstracted, BinderInfo::Default);
        let candidate = kernel.app(f, other_side);
        let ok = kernel.def_eq(candidate, expected);
        if debug {
            eprintln!(
                "  [kabstract] found occurrence; candidate={} expected={} defeq={ok}",
                kernel.render_lean(candidate),
                kernel.render_lean(expected)
            );
        }
        if ok {
            return Some(self.build_congr(kernel, f, hyp_proof, hyp_goal, goal));
        }
        // The single congruence rewrite alone does not close the gap: the
        // wrap `f` was found, but `f(other_side)` is not definitionally the
        // side of the goal it needs to be. This is exactly the "step-case
        // bridge is not a single congruence" shape — e.g. `f = fun x => (1 +
        // n) * x` versus the goal's own `fun x => n.succ * x`, differing only
        // by the arithmetic identity `1 + n = n.succ`. Try to prove THAT
        // residual gap as a standalone, universally-quantified auxiliary
        // lemma and splice it onto the congruence proof with `Eq.trans`.
        let aux = self.try_residual_lemma(
            kernel,
            hyp_goal.level,
            hyp_goal.carrier,
            candidate,
            expected,
            debug,
        )?;
        // `aux : Eq(candidate, expected)`. `build_congr` always returns a
        // proof of `Eq(f(hyp_goal.lhs), f(hyp_goal.rhs))`; `candidate` is
        // `f(hyp_goal.lhs)` when `other_side` was `hyp_goal.lhs` (the RHS
        // branch) and `f(hyp_goal.rhs)` otherwise (the LHS branch), so the
        // two branches need `aux` spliced on opposite sides of `Eq.trans`.
        let congr_proof = self.build_congr(kernel, f, hyp_proof, hyp_goal, goal);
        let a_side = kernel.app(f, hyp_goal.lhs);
        let b_side = kernel.app(f, hyp_goal.rhs);
        Some(if other_is_hyp_lhs {
            // candidate == a_side; aux : Eq(a_side, expected).
            let aux_symm = self.build_eq_symm(
                kernel,
                hyp_goal.level,
                hyp_goal.carrier,
                a_side,
                expected,
                aux,
            );
            self.build_eq_trans(
                kernel,
                hyp_goal.level,
                hyp_goal.carrier,
                expected,
                a_side,
                b_side,
                aux_symm,
                congr_proof,
            )
        } else {
            // candidate == b_side; aux : Eq(b_side, expected).
            self.build_eq_trans(
                kernel,
                hyp_goal.level,
                hyp_goal.carrier,
                a_side,
                b_side,
                expected,
                congr_proof,
                aux,
            )
        })
    }

    /// Generalize the residual gap `Eq(candidate, expected)` back into a
    /// standalone `∀ …, Eq(candidate, expected)` goal over every free
    /// variable this search has minted so far that occurs in either side
    /// (with a KNOWN type, from [`Search::fvar_types`] — a variable whose
    /// type was never recorded makes generalizing it unsound to attempt, so
    /// its presence declines this path rather than guessing), and try to
    /// prove that auxiliary lemma with a nested, budget-sharing call to
    /// [`Search::attempt`]. On success, the returned proof is the lemma
    /// re-applied to the ORIGINAL free variable values, i.e. exactly a proof
    /// of `Eq(candidate, expected)` in the CURRENT scope.
    ///
    /// Bounded by [`MAX_RESIDUAL_LEMMAS`] (decremented on every attempt,
    /// success or failure) so this cannot turn one decline into unbounded
    /// extra search, and the nested `attempt` call shares — rather than
    /// adds to — the outer derivation's [`MAX_BINDERS`]/[`MAX_INDUCTIONS`]
    /// budget, restored afterward regardless of outcome since the lemma is a
    /// self-contained side quest, not a consumer of the primary derivation's
    /// remaining search budget.
    fn try_residual_lemma(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        candidate: ExprId,
        expected: ExprId,
        debug: bool,
    ) -> Option<ExprId> {
        // First, narrow the gap to its actual point of difference, so the
        // lemma this asks for is as small as it can be — `1 + n = n.succ`,
        // say, rather than the whole multiplication surrounding it. Without
        // this, generalizing the ENTIRE (candidate, expected) pair when they
        // share a large common context just re-poses a goal nearly as hard
        // as the original one it is meant to help close, and a nested
        // `attempt` on it can recurse into needing the very same residual
        // again — burning the shared budget without making progress.
        // Both sides need to be in a COMPARABLE reduced form before a
        // structural spine-diff means anything: `candidate` here is a raw,
        // unreduced `App(f, other_side)` beta-redex (`f` a lambda), which has
        // nothing in common structurally with `expected`'s own head shape
        // until both are whnf-forced through to the same underlying
        // operator application.
        let candidate_whnf = kernel.whnf(candidate);
        let expected_whnf = kernel.whnf(expected);
        let mut diff_budget = MAX_DIFF_NODES;
        if let Some((diff_a, diff_b)) =
            find_diff(kernel, candidate_whnf, expected_whnf, &mut diff_budget)
            && !(kernel.def_eq(diff_a, candidate_whnf) && kernel.def_eq(diff_b, expected_whnf))
        {
            let placeholder_fv = self.fresh_fvar();
            let placeholder = kernel.fvar(placeholder_fv);
            let mut kb = MAX_KABSTRACT_NODES;
            let (replaced, found) =
                kabstract_occurrences(kernel, candidate_whnf, diff_a, placeholder, &mut kb);
            if found {
                let anon = kernel.anon();
                let abstracted = kernel.abstract_fvars(replaced, &[placeholder_fv]);
                let g = kernel.lam(anon, carrier, abstracted, BinderInfo::Default);
                let g_diff_b = kernel.app(g, diff_b);
                if kernel.def_eq(g_diff_b, expected_whnf) {
                    if debug {
                        eprintln!(
                            "  [residual] narrowed diff: {} vs {}",
                            kernel.render_lean(diff_a),
                            kernel.render_lean(diff_b)
                        );
                    }
                    if let Some(aux_diff) =
                        self.prove_universal_identity(kernel, level, carrier, diff_a, diff_b, debug)
                    {
                        return Some(self.build_congr_arg(
                            kernel, g, level, carrier, level, carrier, diff_a, diff_b, aux_diff,
                        ));
                    }
                }
            }
        }
        // Fall back to generalizing the whole (candidate, expected) pair —
        // still correct, just less likely to be provable in one shot.
        self.prove_universal_identity(kernel, level, carrier, candidate, expected, debug)
    }

    /// Prove `Eq carrier a b` by generalizing every free variable (with a
    /// KNOWN type, from [`Search::fvar_types`]) occurring in either side back
    /// into a standalone `∀ …, Eq(a, b)` goal, and discharging it with a
    /// nested, budget-sharing call to [`Search::attempt`]. On success,
    /// returns that proof re-applied to the ORIGINAL free-variable values —
    /// i.e. a proof of `Eq carrier a b` in the CURRENT scope.
    ///
    /// Bounded by [`MAX_RESIDUAL_LEMMAS`] (decremented on every attempt,
    /// success or failure). The nested `attempt` call shares — rather than
    /// adds to — the outer derivation's [`MAX_BINDERS`]/[`MAX_INDUCTIONS`]
    /// budget, whose counters are restored afterward regardless of outcome:
    /// the lemma is a self-contained side quest, not a consumer of the
    /// primary derivation's remaining search budget.
    fn prove_universal_identity(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        a: ExprId,
        b: ExprId,
        debug: bool,
    ) -> Option<ExprId> {
        if self.residual_budget == 0 {
            return None;
        }
        self.residual_budget -= 1;

        let mut occurring = std::collections::BTreeSet::new();
        let mut budget = MAX_FVAR_COLLECT_NODES;
        collect_fvars(kernel, a, &mut occurring, &mut budget);
        collect_fvars(kernel, b, &mut occurring, &mut budget);
        if occurring.is_empty() {
            return None;
        }
        let ordered: Vec<u64> = occurring.into_iter().collect();
        let mut types = Vec::with_capacity(ordered.len());
        for v in &ordered {
            types.push(*self.fvar_types.get(v)?);
        }

        let base = build_eq(kernel, self.eqp_eq, level, carrier, a, b);
        let anon = kernel.anon();
        let mut residual_goal = base;
        for (v, ty) in ordered.iter().zip(types.iter()) {
            let abstracted = kernel.abstract_fvars(residual_goal, &[*v]);
            residual_goal = kernel.pi(anon, *ty, abstracted, BinderInfo::Default);
        }
        if debug {
            eprintln!("  [residual] goal={}", kernel.render_lean(residual_goal));
        }

        let snapshot = (
            self.binders_left,
            self.inductions_left,
            self.binders_used,
            self.inductions_used,
        );
        let eqp = EqPrimitives {
            eq: self.eqp_eq,
            eq_refl: self.eqp_refl,
            eq_rec: self.eqp_rec,
        };
        let result = self.attempt(kernel, residual_goal, &eqp, None);
        (
            self.binders_left,
            self.inductions_left,
            self.binders_used,
            self.inductions_used,
        ) = snapshot;
        let residual_proof = match result {
            Ok(proof) => proof,
            Err(reason) => {
                if debug {
                    eprintln!("  [residual] FAILED: {reason}");
                }
                return None;
            }
        };

        // Instantiate outermost-first: each successive `Pi` above was wrapped
        // AROUND the previous body, so the LAST variable generalized is the
        // OUTERMOST binder — apply in the reverse of that order.
        let mut aux = residual_proof;
        for v in ordered.iter().rev() {
            let value = kernel.fvar(*v);
            aux = kernel.app(aux, value);
        }
        if debug {
            eprintln!("  [residual] proved aux={}", kernel.render_lean(aux));
        }
        Some(aux)
    }

    /// `Eq.trans (hab : Eq carrier a b) (hbc : Eq carrier b c) : Eq carrier a
    /// c`, built directly from `Eq.rec` — no hand-written `Eq.trans` theorem
    /// exists in an isolated statement-import kernel either.
    #[allow(clippy::too_many_arguments, clippy::many_single_char_names)]
    fn build_eq_trans(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        hab: ExprId,
        hbc: ExprId,
    ) -> ExprId {
        let anon = kernel.anon();
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let concl = build_eq(kernel, self.eqp_eq, level, carrier, a, x);
        let hyp_ty = build_eq(kernel, self.eqp_eq, level, carrier, b, x);
        let anon_hyp = kernel.anon();
        let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
        let motive = lam_fv(kernel, anon, x_fv, carrier, inner, BinderInfo::Default);
        let z = kernel.level_zero();
        let rec = kernel.const_(self.eqp_rec, vec![z, level]);
        let with_carrier = kernel.app(rec, carrier);
        let with_a = kernel.app(with_carrier, b);
        let with_motive = kernel.app(with_a, motive);
        let with_minor = kernel.app(with_motive, hab);
        let with_c = kernel.app(with_minor, c);
        kernel.app(with_c, hbc)
    }

    /// `Eq.symm (h : Eq carrier a b) : Eq carrier b a`, built directly from
    /// `Eq.rec`, for the same reason [`Search::build_eq_trans`] is.
    #[allow(clippy::many_single_char_names)]
    fn build_eq_symm(
        &mut self,
        kernel: &mut Kernel,
        level: LevelId,
        carrier: ExprId,
        a: ExprId,
        b: ExprId,
        h: ExprId,
    ) -> ExprId {
        let anon = kernel.anon();
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let concl = build_eq(kernel, self.eqp_eq, level, carrier, x, a);
        let hyp_ty = build_eq(kernel, self.eqp_eq, level, carrier, a, x);
        let anon_hyp = kernel.anon();
        let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
        let motive = lam_fv(kernel, anon, x_fv, carrier, inner, BinderInfo::Default);
        let refl_a = build_eq_refl(kernel, self.eqp_refl, level, carrier, a);
        let z = kernel.level_zero();
        let rec = kernel.const_(self.eqp_rec, vec![z, level]);
        let with_carrier = kernel.app(rec, carrier);
        let with_a = kernel.app(with_carrier, a);
        let with_motive = kernel.app(with_a, motive);
        let with_minor = kernel.app(with_motive, refl_a);
        let with_b = kernel.app(with_minor, b);
        kernel.app(with_b, h)
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
        self.build_congr_arg(
            kernel,
            f,
            hyp_goal.level,
            hyp_goal.carrier,
            goal.level,
            goal.carrier,
            hyp_goal.lhs,
            hyp_goal.rhs,
            hyp_proof,
        )
    }

    /// `congrArg f hab : Eq out_carrier (f a) (f b)`, given `f : in_carrier ->
    /// out_carrier` and `hab : Eq in_carrier a b` — built directly from the
    /// kernel's generated `Eq.rec`, generalized out of [`Search::build_congr`]
    /// so the residual-lemma path ([`Search::try_residual_lemma`]) can build
    /// a SECOND congruence step (wrapping a narrowed auxiliary identity back
    /// up to the shape the primary rewrite needed) with the same primitive.
    #[allow(clippy::too_many_arguments, clippy::many_single_char_names)]
    fn build_congr_arg(
        &mut self,
        kernel: &mut Kernel,
        f: ExprId,
        in_level: LevelId,
        in_carrier: ExprId,
        out_level: LevelId,
        out_carrier: ExprId,
        a: ExprId,
        b: ExprId,
        hab: ExprId,
    ) -> ExprId {
        let anon = kernel.anon();
        let fa = kernel.app(f, a);
        // motive := fun (x : in_carrier) (_ : Eq in_level in_carrier a x) =>
        //             Eq out_level out_carrier fa (f x)
        let x_fv = self.fresh_fvar();
        let x = kernel.fvar(x_fv);
        let fx = kernel.app(f, x);
        let concl = build_eq(kernel, self.eqp_eq, out_level, out_carrier, fa, fx);
        let hyp_ty = build_eq(kernel, self.eqp_eq, in_level, in_carrier, a, x);
        let anon_hyp = kernel.anon();
        let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
        let motive = lam_fv(kernel, anon, x_fv, in_carrier, inner, BinderInfo::Default);
        let refl_case = build_eq_refl(kernel, self.eqp_refl, out_level, out_carrier, fa);
        let z = kernel.level_zero();
        let rec = kernel.const_(self.eqp_rec, vec![z, in_level]);
        let with_carrier = kernel.app(rec, in_carrier);
        let with_a = kernel.app(with_carrier, a);
        let with_motive = kernel.app(with_a, motive);
        let with_minor = kernel.app(with_motive, refl_case);
        let with_b = kernel.app(with_minor, b);
        kernel.app(with_b, hab)
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
        let x_fv = self.fresh_fvar_typed(binder_ty);
        let x = kernel.fvar(x_fv);
        let prop_at_x = kernel.instantiate(body, &[x]);
        let motive = lam_fv(kernel, anon, x_fv, binder_ty, prop_at_x, binder_info);

        // Base case: prove the goal at `zero`. Recursing through `attempt`
        // (rather than assuming `body` is already a bare `Eq`) lets this
        // close goals where further binders — plain hypotheses, or another
        // zero/succ-shaped variable — follow the induction variable.
        let base_goal_expr = kernel.instantiate(body, &[zero_e]);
        if std::env::var("BIS_DEBUG").is_ok() {
            eprintln!(
                "try_induction: binder={} base_goal={}",
                kernel.display_name(binder_name),
                kernel.render_lean(base_goal_expr)
            );
        }
        let case_zero = self
            .attempt(kernel, base_goal_expr, eqp, hypothesis)
            .inspect_err(|e| {
                if std::env::var("BIS_DEBUG").is_ok() {
                    eprintln!("  base case FAILED: {e}");
                }
            })?;

        // Step case: fresh predecessor + induction hypothesis, prove the goal
        // at `succ pred`. The hypothesis carries `body` instantiated at
        // `pred` verbatim — still possibly `Pi`-headed — and is peeled in
        // lockstep with the goal by `instantiate_hypothesis` as `attempt`
        // generalizes any further binders below.
        let pred_fv = self.fresh_fvar_typed(binder_ty);
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
        if std::env::var("BIS_DEBUG").is_ok() {
            eprintln!(
                "try_induction: binder={} step_goal={} ih={}",
                kernel.display_name(binder_name),
                kernel.render_lean(step_goal_expr),
                kernel.render_lean(pred_goal_expr)
            );
        }
        let step_proof = self
            .attempt(kernel, step_goal_expr, eqp, Some(step_ih))
            .inspect_err(|e| {
                if std::env::var("BIS_DEBUG").is_ok() {
                    eprintln!("  step case FAILED: {e}");
                }
            })?;
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
            let fv = self.fresh_fvar_typed(ty);
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
        fvar_types: std::collections::BTreeMap::new(),
        residual_budget: MAX_RESIDUAL_LEMMAS,
    };
    let proof = search.attempt(kernel, goal, &eqp, None)?;
    Ok(Candidate {
        proof,
        binders_used: search.binders_used,
        inductions_used: search.inductions_used,
    })
}
