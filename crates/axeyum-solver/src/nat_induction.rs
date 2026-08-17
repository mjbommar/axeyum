//! Natural-number induction over a negated universal goal.
//!
//! The adversarial reachability census
//! (`docs/mathematics-2026-08/04-reachability.md` R3) ranks `induction-over-nat`
//! first among out-of-fragment requests — 16 rows, double the next entry — and
//! it is the only entry on that list that is not a *missing logic*. The kernel
//! has an inductive `Nat` with an ι-computing `Nat.rec`;
//! `axeyum-lean-kernel/tests/induction_arrow.rs` establishes that a caller can
//! drive it to an admitted theorem from outside the crate. What was missing was
//! any solver route that produces the two obligations to feed it.
//!
//! [`quant_valid_universal`](crate::quant_valid_universal) already decides a
//! universal whose body is valid *by theory alone* — `∀x:Int. x + 0 == x` —
//! by Skolemising and refuting the negated body. Induction is needed exactly
//! where that fails: when the body mentions a function the theory does not
//! interpret, pinned only by recursion equations. `f(0) = 0` together with
//! `∀k ≥ 0. f(k+1) = f(k) + (k+1)` does not entail `∀n ≥ 0. 2·f(n) = n·(n+1)`
//! in LIA+UF, because nothing forces the unrolling to reach every `n`.
//!
//! # What this pass does
//!
//! Given assertions containing exactly one negated universal `¬∀n. body` — the
//! SMT idiom for "prove the universal" — it discharges the two obligations with
//! the *existing* quantifier-free dispatch and concludes `unsat` only if both
//! come back definitively `unsat`:
//!
//! ```text
//! base:  hyps ∧ ¬concl[n := 0]                       unsat
//! step:  hyps ∧ k ≥ 0 ∧ concl[n := k] ∧ ¬concl[n := k+1]   unsat
//! ```
//!
//! # Soundness
//!
//! The pass can only ever *add* an `unsat`. `k` is a fresh unconstrained
//! constant, so refuting the step body proves the implication for every
//! non-negative integer. Base and step together give `∀n ≥ 0. concl(n)` by
//! induction, so the negated universal in the assertion set is unsatisfiable,
//! so the set is. Every other assertion is carried into both sub-checks as a
//! hypothesis, which is sound because they are assumed in the original query.
//!
//! If either obligation comes back `sat` or `unknown` the pass returns `None`
//! and the query proceeds through the other routes unchanged — a failed
//! induction is never evidence of satisfiability, only of this route not
//! applying.
//!
//! # Instantiation
//!
//! Universally-quantified hypotheses are instantiated at the points the two
//! obligations need — `0` for the base, and `k` and `k+1` for the step — rather
//! than left quantified. Nothing here searches for triggers: the induction
//! variable supplies the instantiation points, which is the whole reason this
//! route can be a single bounded pass instead of a saturation loop.

use std::collections::HashMap;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};

/// The recognised shape: which assertion is the goal, and the goal's parts.
struct Goal {
    /// Index into `assertions` of the `¬∀n. body` assertion.
    index: usize,
    /// The bound variable `n`.
    var: axeyum_ir::SymbolId,
    /// The body under the quantifier, with any `n ≥ 0` guard stripped.
    conclusion: TermId,
}

/// Peel `¬∀n. body`, returning the goal when exactly one assertion has that
/// shape over an `Int` variable.
///
/// Exactly one, deliberately. Two negated universals is a disjunctive
/// obligation this pass does not model, and picking one of them would be
/// choosing which theorem to prove.
fn recognise(arena: &TermArena, assertions: &[TermId]) -> Option<Goal> {
    let mut found: Option<Goal> = None;
    for (index, &assertion) in assertions.iter().enumerate() {
        let TermNode::App {
            op: Op::BoolNot,
            args,
        } = arena.node(assertion)
        else {
            continue;
        };
        let inner = args[0];
        let TermNode::App {
            op: Op::Forall(var),
            args: body_args,
        } = arena.node(inner)
        else {
            continue;
        };
        if arena.symbol(*var).1 != Sort::Int {
            continue;
        }
        let body = body_args[0];
        if contains_quantifier(arena, body) {
            continue; // nested quantifier: not this pass's shape
        }
        if found.is_some() {
            return None; // two goals — see the doc comment
        }
        // No `n ≥ 0` guard ⇒ the goal is universal over all of `Int`, which
        // ℕ-induction cannot establish. Decline rather than answer.
        let Some(conclusion) = strip_nonneg_guard(arena, body, *var) else {
            continue;
        };
        found = Some(Goal {
            index,
            var: *var,
            conclusion,
        });
    }
    found
}

/// `(=> (>= n 0) concl)` ⇒ `Some(concl)`; **`None` for anything else**.
///
/// Returning `None` — rather than the body unchanged — is a soundness
/// requirement, not a stylistic one.
///
/// This function used to fall through to `body`, and the route proceeded. But
/// base plus step establishes `∀n ≥ 0. concl(n)`, while the goal quantifies
/// over all of `Int`. On
///
/// ```smt2
/// (assert (not (forall ((n Int)) (>= n 0))))
/// ```
///
/// the base `0 ≥ 0` and the step `k ≥ 0 → k+1 ≥ 0` both discharge, so the route
/// answered `unsat` on an assertion set that is **satisfiable** — witness
/// `n = -1`, which this repository's own front door returns. A wrong `unsat`
/// is the worst failure this project can produce, and ℕ-induction applied to an
/// `Int`-quantified goal produces it by construction.
///
/// So the guard is now mandatory: no recognised `n ≥ 0`, no induction. A goal
/// genuinely universal over `Int` needs a different argument (two-sided
/// induction, or a decision procedure), not this one.
fn strip_nonneg_guard(arena: &TermArena, body: TermId, var: axeyum_ir::SymbolId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [guard, rest] = args.as_ref() else {
        return None;
    };
    is_nonneg_guard(arena, *guard, var).then_some(*rest)
}

/// Whether `guard` is `n >= 0` (or `0 <= n`) for this `var`.
///
/// The operands are destructured by an **exactly-two** slice pattern, not by
/// indexing. `args[1]` before the operator is known was an index-out-of-bounds
/// panic on any one-argument guard — `(=> (not (= n 5)) …)` is legal SMT-LIB and
/// crashed the route (`tests/nat_induction_adversarial.rs::guard_negation_one_arg`).
/// A route in dispatch turns that from an unreachable diagnostic into a front-door
/// crash, so the arity is checked, not assumed.
fn is_nonneg_guard(arena: &TermArena, guard: TermId, var: axeyum_ir::SymbolId) -> bool {
    let TermNode::App { op, args } = arena.node(guard) else {
        return false;
    };
    let [left, right] = args.as_ref() else {
        return false;
    };
    let is_var = |t: TermId| matches!(arena.node(t), TermNode::Symbol(s) if *s == var);
    let is_zero = |t: TermId| matches!(arena.node(t), TermNode::IntConst(0));
    match op {
        Op::IntGe => is_var(*left) && is_zero(*right),
        Op::IntLe => is_zero(*left) && is_var(*right),
        _ => false,
    }
}

fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App { op, args } => {
            matches!(op, Op::Forall(_) | Op::Exists(_))
                || args.iter().any(|&a| contains_quantifier(arena, a))
        }
        _ => false,
    }
}

/// Substitute `var := value` throughout `term`.
fn at(
    arena: &mut TermArena,
    term: TermId,
    var: axeyum_ir::SymbolId,
    value: TermId,
) -> Result<TermId, SolverError> {
    let var_term = arena.var(var);
    let replacements: HashMap<TermId, TermId> = [(var_term, value)].into_iter().collect();
    let mut memo = HashMap::new();
    replace_subterms(arena, term, &replacements, &mut memo)
        .map_err(|e| SolverError::Backend(e.to_string()))
}

/// Hypotheses for one obligation: every non-goal assertion, with universals
/// instantiated at each of `points`.
///
/// A universal hypothesis is **replaced** by its instantiations rather than
/// accompanied by them; see the note at the substitution site for why retaining
/// it defeats the pass.
fn hypotheses(
    arena: &mut TermArena,
    assertions: &[TermId],
    goal: &Goal,
    points: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let mut out = Vec::new();
    for (index, &assertion) in assertions.iter().enumerate() {
        if index == goal.index {
            continue;
        }
        let TermNode::App {
            op: Op::Forall(var),
            args,
        } = arena.node(assertion)
        else {
            out.push(assertion); // ground hypothesis: carried as-is
            continue;
        };
        let (var, body) = (*var, args[0]);
        if arena.symbol(var).1 != Sort::Int || contains_quantifier(arena, body) {
            out.push(assertion);
            continue;
        }
        // REPLACED by its instantiations, not accompanied by them. Retaining the
        // quantifier leaves the sub-query quantified, which sends `check_auto`
        // to the quantifier front door and yields `unknown` — measured: with the
        // original retained, the closed form of a `f(k+1) = f(k) + 2` recurrence
        // was not discharged even though every instance it needs was present.
        // Dropping it can only weaken the hypotheses, and this pass may only
        // ever conclude `unsat`, so a weaker hypothesis set costs completeness
        // and never soundness.
        for &point in points {
            let instance = at(arena, body, var, point)?;
            out.push(instance);
        }
    }
    Ok(out)
}

/// Decide `query` with the quantifier-free dispatch; `true` only on a
/// definitive `unsat`.
fn refuted(
    arena: &mut TermArena,
    query: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    match check_auto(arena, query, config) {
        Ok(CheckResult::Unsat) => Ok(true),
        // Sat, unknown, and an unsupported sub-query are all "this route does
        // not apply" — never evidence of satisfiability, only of not proving.
        Ok(CheckResult::Sat(_) | CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            Ok(false)
        }
        Err(error) => Err(error),
    }
}

/// Try to refute the assertion set by induction on the single negated universal.
///
/// Returns `Some(CheckResult::Unsat)` when both obligations are discharged, and
/// `None` in every other case — including "recognised the shape but could not
/// discharge it", which is why this can be run speculatively.
///
/// # Errors
///
/// Propagates a hard backend error from either obligation.
pub fn prove_by_nat_induction(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let Some(goal) = recognise(arena, assertions) else {
        return Ok(None);
    };

    // Base: hyps ∧ ¬concl(0).
    let zero = arena.int_const(0);
    let base_case = at(arena, goal.conclusion, goal.var, zero)?;
    let negated_base = arena
        .not(base_case)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let mut base_query = hypotheses(arena, assertions, &goal, &[zero])?;
    base_query.push(negated_base);
    if !refuted(arena, &base_query, config)? {
        return Ok(None);
    }

    // Step: hyps ∧ k ≥ 0 ∧ concl(k) ∧ ¬concl(k+1), for fresh unconstrained `k`.
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let k_symbol = arena.declare_internal("!ind_k", Sort::Int).map_err(err)?;
    let k = arena.var(k_symbol);
    let one = arena.int_const(1);
    let k_plus_one = arena.int_add(k, one).map_err(err)?;

    let k_nonneg = arena.int_ge(k, zero).map_err(err)?;
    let at_k = at(arena, goal.conclusion, goal.var, k)?;
    let at_k1 = at(arena, goal.conclusion, goal.var, k_plus_one)?;
    let negated_step = arena.not(at_k1).map_err(err)?;

    let mut step_query = hypotheses(arena, assertions, &goal, &[k, k_plus_one])?;
    step_query.push(k_nonneg);
    step_query.push(at_k);
    step_query.push(negated_step);
    if !refuted(arena, &step_query, config)? {
        return Ok(None);
    }

    Ok(Some(CheckResult::Unsat))
}
