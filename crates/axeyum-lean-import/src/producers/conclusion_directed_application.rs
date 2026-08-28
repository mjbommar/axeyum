//! Untrusted, bounded **conclusion-directed** application search.
//!
//! [`producers::bounded_application`](super::bounded_application) grows a
//! forward product closure: every candidate applied to every typed term, one
//! layer at a time. That is complete for small arities and structurally
//! blind past them — the closure grows like `arguments ^ depth`, so its
//! 128-term budget is exhausted at application depth 4 with only four
//! `Nat`-typed goal binders in scope. Measured 2026-08-28 over the ten open
//! `natural-modular-equivalence` targets: the two hypothesis-free members
//! (`Nat.mod_modEq`, `Nat.modEq_one`) closed at depth 2, and all eight members
//! carrying a congruence hypothesis declined with `NoTypedApplication`, every
//! one of them needing a five-argument application the budget cannot reach.
//!
//! This producer inverts the direction. It peels the goal's leading `Pi`
//! binders into free variables exactly as the forward search does, then for
//! each supplied declaration peels *that* declaration's binders into **holes**
//! and first-order-matches the declaration's conclusion against the goal's
//! terminal. Matching fixes the holes the conclusion mentions; each remaining
//! hole is discharged from the goal's own binders by definitional equality, in
//! goal-binder order. The result is one application per candidate rather than
//! a closure, so cost is linear in `candidates x arguments x goal binders` and
//! independent of arity.
//!
//! Nothing here is trusted. First-order matching is a *heuristic for choosing
//! arguments*; the constructed term is type-checked by
//! [`Kernel::infer_in`](axeyum_lean_kernel::Kernel::infer_in) and required to
//! be [`Kernel::def_eq`](axeyum_lean_kernel::Kernel::def_eq) to the goal
//! before it is returned, and the caller still has to re-admit it through
//! `Kernel::add_declaration`. A wrong match produces a decline, never an
//! admitted theorem.
//!
//! This module never names a theory, a carrier, or a target: it reads the
//! goal's own binders and the caller's own declaration list, and every `Const`
//! node it builds names a declaration the caller supplied.

use std::collections::{HashMap, HashSet};

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, LocalContext, LocalDecl, NameId,
};

/// Maximum leading `Pi` binders peeled from the goal.
pub const MAX_GOAL_BINDERS: usize = 12;
/// Maximum leading `Pi` binders peeled from one candidate declaration.
pub const MAX_HOLES: usize = 16;

/// First free-variable id minted for a peeled **goal** binder. Chosen clear of
/// `bounded_application` (`9_100_000`), `bounded_induction` (`9_000_000`),
/// `trusted_substitution` (`900_000_000`) and `modeq_family`
/// (`9_500_000_000`), so no two producers' variables can collide in one
/// process.
const GOAL_FVAR_BASE: u64 = 9_700_000_000;
/// First free-variable id minted for a candidate **hole**, kept disjoint from
/// `GOAL_FVAR_BASE` by more than `MAX_GOAL_BINDERS`.
const HOLE_FVAR_BASE: u64 = 9_800_000_000;

/// One fully constructed candidate, valid only in the kernel that built it.
#[derive(Debug, Clone, Copy)]
pub struct Candidate {
    /// The proposed proof term. Untrusted until re-admitted.
    pub proof: ExprId,
    /// Leading goal binders peeled before matching.
    pub goal_binders: usize,
    /// Holes the winning candidate declaration exposed.
    pub holes: usize,
    /// Holes fixed by matching the conclusion (the rest came from the goal's
    /// own binders by definitional equality).
    pub holes_matched: usize,
    /// Candidate declarations examined before one succeeded, inclusive.
    pub declarations_tried: usize,
}

/// Typed reason the bounded search declined. A decline is an ordinary
/// outcome, not a failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclineReason {
    /// The goal has more leading `Pi` binders than [`MAX_GOAL_BINDERS`].
    GoalBinderBudgetExceeded,
    /// Every supplied declaration exposed more binders than [`MAX_HOLES`].
    HoleBudgetExceeded,
    /// No supplied declaration is a universe-monomorphic `Definition` or
    /// `Theorem` this search can apply.
    NoUsableCandidates,
    /// Some declaration was usable, but none produced a term the kernel
    /// accepts as a proof of the goal.
    NoConclusionMatch,
}

impl std::fmt::Display for DeclineReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::GoalBinderBudgetExceeded => {
                write!(f, "goal exceeds the {MAX_GOAL_BINDERS}-binder budget")
            }
            Self::HoleBudgetExceeded => {
                write!(f, "every candidate exceeds the {MAX_HOLES}-hole budget")
            }
            Self::NoUsableCandidates => {
                write!(f, "no supplied zero-universe declaration is usable")
            }
            Self::NoConclusionMatch => write!(
                f,
                "no candidate conclusion matched the goal with every remaining hole discharged"
            ),
        }
    }
}

impl std::error::Error for DeclineReason {}

#[derive(Debug, Clone, Copy)]
struct Binder {
    name: NameId,
    ty: ExprId,
    info: BinderInfo,
    fvar: u64,
}

fn local_context(binders: &[Binder]) -> LocalContext {
    let mut context = LocalContext::new();
    for binder in binders {
        context.push(LocalDecl {
            fvar: binder.fvar,
            name: binder.name,
            ty: binder.ty,
            info: binder.info,
        });
    }
    context
}

fn close_binders(kernel: &mut Kernel, binders: &[Binder], mut proof: ExprId) -> ExprId {
    for binder in binders.iter().rev() {
        let body = kernel.abstract_fvars(proof, &[binder.fvar]);
        proof = kernel.lam(binder.name, binder.ty, body, binder.info);
    }
    proof
}

fn introduce_goal_binders(
    kernel: &mut Kernel,
    goal: ExprId,
) -> Result<(Vec<Binder>, ExprId), DeclineReason> {
    let mut binders = Vec::new();
    let mut terminal = goal;
    loop {
        let reduced = kernel.whnf(terminal);
        let ExprNode::Pi(name, ty, body, info) = kernel.expr_node(reduced).clone() else {
            return Ok((binders, reduced));
        };
        if binders.len() == MAX_GOAL_BINDERS {
            return Err(DeclineReason::GoalBinderBudgetExceeded);
        }
        let fvar = GOAL_FVAR_BASE + binders.len() as u64;
        let value = kernel.fvar(fvar);
        terminal = kernel.instantiate(body, &[value]);
        binders.push(Binder {
            name,
            ty,
            info,
            fvar,
        });
    }
}

/// Whether `expression` mentions any free variable in `holes`.
///
/// Memoised on `ExprId`: expressions are an interned DAG here, so the naive
/// recursion re-walks shared subterms and is exponential in sharing depth,
/// not linear in size. That is not a micro-optimisation — the unmemoised form
/// took over 200 s per target on the `Nat.ModEq` congruence goals, whose
/// `HMod`/`HAdd` instance spines are heavily shared.
fn mentions_hole(
    kernel: &Kernel,
    expression: ExprId,
    holes: &HashSet<u64>,
    memo: &mut HashMap<ExprId, bool>,
) -> bool {
    if let Some(known) = memo.get(&expression) {
        return *known;
    }
    let answer = match kernel.expr_node(expression) {
        ExprNode::FVar(id) => holes.contains(id),
        ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::Const(_, _) | ExprNode::Lit(_) => false,
        ExprNode::Proj(_, _, inner) => {
            let inner = *inner;
            mentions_hole(kernel, inner, holes, memo)
        }
        ExprNode::App(function, argument) => {
            let (function, argument) = (*function, *argument);
            mentions_hole(kernel, function, holes, memo)
                || mentions_hole(kernel, argument, holes, memo)
        }
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
            let (ty, body) = (*ty, *body);
            mentions_hole(kernel, ty, holes, memo) || mentions_hole(kernel, body, holes, memo)
        }
        ExprNode::Let(_, ty, value, body) => {
            let (ty, value, body) = (*ty, *value, *body);
            mentions_hole(kernel, ty, holes, memo)
                || mentions_hole(kernel, value, holes, memo)
                || mentions_hole(kernel, body, holes, memo)
        }
    };
    memo.insert(expression, answer);
    answer
}

/// One assignment slot per peeled hole, in the candidate's own binder order.
type Assignment = Vec<Option<ExprId>>;

/// Mutable state threaded through one candidate's match attempt.
struct MatchState<'holes> {
    holes: &'holes HashSet<u64>,
    arity: usize,
    assignment: Assignment,
    hole_memo: HashMap<ExprId, bool>,
}

impl MatchState<'_> {
    fn hole_slot(&self, id: u64) -> Option<usize> {
        let slot = usize::try_from(id.checked_sub(HOLE_FVAR_BASE)?).ok()?;
        (slot < self.arity).then_some(slot)
    }
}

/// First-order match `pattern` (which may mention holes) against `target`.
///
/// A hole matches anything and is then pinned: a second occurrence must be
/// [`Kernel::def_eq`] to the first. A hole-free pattern subterm is compared by
/// definitional equality, which is what lets two independently elaborated but
/// definitionally equal instance paths agree. A subterm that still mentions a
/// hole must match structurally, because `def_eq` cannot solve for a hole —
/// and `whnf` is applied only when the raw structural comparison fails, since
/// weak-head-normalising every node of an instance spine is what made the
/// first version of this search unusable.
fn match_pattern(
    kernel: &mut Kernel,
    pattern: ExprId,
    target: ExprId,
    state: &mut MatchState<'_>,
    may_reduce: bool,
) -> bool {
    if let ExprNode::FVar(id) = kernel.expr_node(pattern)
        && let Some(slot) = state.hole_slot(*id)
    {
        return if let Some(existing) = state.assignment[slot] {
            kernel.def_eq(existing, target)
        } else {
            state.assignment[slot] = Some(target);
            true
        };
    }
    if !mentions_hole(kernel, pattern, state.holes, &mut state.hole_memo) {
        return pattern == target || kernel.def_eq(pattern, target);
    }
    let structural = match (
        kernel.expr_node(pattern).clone(),
        kernel.expr_node(target).clone(),
    ) {
        (ExprNode::App(pf, pa), ExprNode::App(tf, ta)) => {
            match_pattern(kernel, pf, tf, state, may_reduce)
                && match_pattern(kernel, pa, ta, state, may_reduce)
        }
        (ExprNode::Lam(_, pt, pb, _), ExprNode::Lam(_, tt, tb, _))
        | (ExprNode::Pi(_, pt, pb, _), ExprNode::Pi(_, tt, tb, _)) => {
            match_pattern(kernel, pt, tt, state, may_reduce)
                && match_pattern(kernel, pb, tb, state, may_reduce)
        }
        (ExprNode::Proj(pn, pi, pe), ExprNode::Proj(tn, ti, te)) => {
            pn == tn && pi == ti && match_pattern(kernel, pe, te, state, may_reduce)
        }
        (ExprNode::Let(_, pt, pv, pb), ExprNode::Let(_, tt, tv, tb)) => {
            match_pattern(kernel, pt, tt, state, may_reduce)
                && match_pattern(kernel, pv, tv, state, may_reduce)
                && match_pattern(kernel, pb, tb, state, may_reduce)
        }
        (ExprNode::Const(pn, pl), ExprNode::Const(tn, tl)) => pn == tn && pl == tl,
        (ExprNode::FVar(a), ExprNode::FVar(b)) => a == b,
        (ExprNode::BVar(a), ExprNode::BVar(b)) => a == b,
        (ExprNode::Sort(a), ExprNode::Sort(b)) => a == b,
        (ExprNode::Lit(a), ExprNode::Lit(b)) => a == b,
        _ => false,
    };
    if structural || !may_reduce {
        return structural;
    }
    let reduced_pattern = kernel.whnf(pattern);
    let reduced_target = kernel.whnf(target);
    if reduced_pattern == pattern && reduced_target == target {
        return false;
    }
    match_pattern(kernel, reduced_pattern, reduced_target, state, false)
}

/// Peel `ty`'s leading `Pi` binders into fresh hole free variables.
fn peel_holes(kernel: &mut Kernel, ty: ExprId) -> Option<(Vec<u64>, ExprId)> {
    let mut holes = Vec::new();
    let mut terminal = ty;
    loop {
        let reduced = kernel.whnf(terminal);
        let ExprNode::Pi(_, _, body, _) = kernel.expr_node(reduced).clone() else {
            return Some((holes, reduced));
        };
        if holes.len() == MAX_HOLES {
            return None;
        }
        let fvar = HOLE_FVAR_BASE + holes.len() as u64;
        let value = kernel.fvar(fvar);
        terminal = kernel.instantiate(body, &[value]);
        holes.push(fvar);
    }
}

/// Maximum argument choices explored while discharging the holes the
/// conclusion did not determine.
pub const MAX_DISCHARGE_ATTEMPTS: usize = 4096;

/// Build `declaration` applied to one argument per hole, taking matched
/// arguments from `assignment` and **backtracking** over the goal's own
/// binders for the rest.
///
/// Backtracking is what a first-pass version got wrong and it is not an
/// optimisation: a conclusion routinely fails to determine every hole. Five
/// of the ten `natural-modular-equivalence` targets measured 2026-08-28 are
/// of that shape — `Nat.ModEq.add_left_cancel'` concludes `a ≡ b [MOD n]`
/// and never mentions the cancelled summand `c`, `Nat.ModEq.of_dvd` concludes
/// modulo `m` and never mentions `n`. Taking the first type-compatible binder
/// picks `n` for `c`, and every one of those five declined. Trying each
/// binder in turn, pruned by the domain type and finally by the kernel's own
/// verdict on the completed application, closes all five.
#[allow(clippy::too_many_arguments)]
fn discharge(
    kernel: &mut Kernel,
    context: &mut LocalContext,
    term: ExprId,
    ty: ExprId,
    slot: usize,
    arity: usize,
    terminal: ExprId,
    assignment: &Assignment,
    binders: &[Binder],
    attempts: &mut usize,
) -> Option<ExprId> {
    if slot == arity {
        return kernel.def_eq(ty, terminal).then_some(term);
    }
    let reduced = kernel.whnf(ty);
    let ExprNode::Pi(_, domain, body, _) = kernel.expr_node(reduced).clone() else {
        return None;
    };
    let choices: Vec<ExprId> = match assignment[slot] {
        Some(value) => vec![value],
        None => binders
            .iter()
            .map(|binder| kernel.fvar(binder.fvar))
            .collect(),
    };
    for argument in choices {
        if *attempts >= MAX_DISCHARGE_ATTEMPTS {
            return None;
        }
        *attempts += 1;
        let Ok(argument_ty) = kernel.infer_in(argument, context) else {
            continue;
        };
        if !kernel.def_eq(argument_ty, domain) {
            continue;
        }
        let next_term = kernel.app(term, argument);
        let next_ty = kernel.instantiate(body, &[argument]);
        if let Some(found) = discharge(
            kernel,
            context,
            next_term,
            next_ty,
            slot + 1,
            arity,
            terminal,
            assignment,
            binders,
            attempts,
        ) {
            return Some(found);
        }
    }
    None
}

/// Propose a proof of `goal` by matching one of `declarations`' conclusions
/// against the goal's terminal.
///
/// The declaration list is the caller's retrieval boundary: this function
/// never scans the environment and never infers a target name from the goal.
///
/// # Errors
///
/// Returns a typed [`DeclineReason`] when no supplied declaration yields a
/// term the kernel accepts. A decline proves nothing and is not an error.
pub fn propose_conclusion_directed_application(
    kernel: &mut Kernel,
    goal: ExprId,
    declarations: &[NameId],
) -> Result<Candidate, DeclineReason> {
    let (binders, terminal) = introduce_goal_binders(kernel, goal)?;
    let mut context = local_context(&binders);

    let mut names = Vec::with_capacity(declarations.len());
    for &name in declarations {
        if names.contains(&name) {
            continue;
        }
        let Some(declaration) = kernel.environment().get(name) else {
            continue;
        };
        if declaration.uparams().is_empty()
            && matches!(
                declaration,
                Declaration::Definition { .. } | Declaration::Theorem { .. }
            )
        {
            names.push(name);
        }
    }
    if names.is_empty() {
        return Err(DeclineReason::NoUsableCandidates);
    }

    let mut any_peeled = false;
    for (index, name) in names.iter().enumerate() {
        let head = kernel.const_(*name, vec![]);
        let Ok(head_ty) = kernel.infer_in(head, &mut context) else {
            continue;
        };
        let Some((holes, conclusion)) = peel_holes(kernel, head_ty) else {
            continue;
        };
        any_peeled = true;
        let hole_set: HashSet<u64> = holes.iter().copied().collect();
        let arity = holes.len();
        let mut state = MatchState {
            holes: &hole_set,
            arity,
            assignment: vec![None; arity],
            hole_memo: HashMap::new(),
        };
        if !match_pattern(kernel, conclusion, terminal, &mut state, true) {
            continue;
        }
        let assignment = state.assignment;
        let holes_matched = assignment.iter().filter(|slot| slot.is_some()).count();
        // Matching only CHOSE the arguments. `discharge` accepts a completed
        // application only when the kernel agrees its type is the goal, so a
        // wrong match backtracks or declines and never reaches the caller.
        let head_term = kernel.const_(*name, vec![]);
        let Ok(head_term_ty) = kernel.infer_in(head_term, &mut context) else {
            continue;
        };
        let mut attempts = 0usize;
        let Some(term) = discharge(
            kernel,
            &mut context,
            head_term,
            head_term_ty,
            0,
            arity,
            terminal,
            &assignment,
            &binders,
            &mut attempts,
        ) else {
            continue;
        };
        return Ok(Candidate {
            proof: close_binders(kernel, &binders, term),
            goal_binders: binders.len(),
            holes: arity,
            holes_matched,
            declarations_tried: index + 1,
        });
    }
    if any_peeled {
        Err(DeclineReason::NoConclusionMatch)
    } else {
        Err(DeclineReason::HoleBudgetExceeded)
    }
}
