//! Low-memory lazy abstraction-refinement BV strategy (ADR-0019).
//!
//! The eager bit-blaster's memory is dominated by **multiplier and divider
//! circuits** (a width-`w` `bvmul` is a quadratic shift-and-add; the
//! `bvudiv`/`bvurem` family is a per-bit restoring divider — both are the
//! heaviest gadgets, measured at thousands of AIG AND-nodes each). This strategy
//! avoids materializing them unless they matter:
//!
//! 1. **Abstract** every heavy subterm — `bvmul`, `bvudiv`, `bvurem`, `bvsdiv`,
//!    `bvsrem`, `bvsmod` — by a fresh, unconstrained variable of the same sort.
//!    Dropping the defining constraint *enlarges* the solution set, so the
//!    abstraction is a sound **over-approximation**.
//! 2. **Solve** the (much smaller) abstraction with the eager pure-Rust path.
//!    - `unsat` ⇒ the original is `unsat` (over-approximation), with **no heavy
//!      gadget ever bit-blasted**.
//!    - `sat` ⇒ **replay** the original assertions under the model. If they hold,
//!      it is a genuine model. Otherwise the abstraction exploited a fresh
//!      variable whose value differs from the real operation result: **refine**
//!      those operations by adding their exact `fresh == op(lhs, rhs)` constraint
//!      (bit-blasting only those), and re-solve.
//!
//! Refinement only ever adds operations, so after at most one round per heavy
//! gadget the problem is fully precise (equivalent to the eager strategy): the
//! loop is **sound, complete, and terminating**, with memory ≤ eager and often
//! far less. Every `sat` is replayed (the trust anchor); `unsat` is sound by the
//! over-approximation argument and cross-checked against the eager strategy in
//! tests.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Op, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::replace_subterms;

use crate::auto::solve;
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

const FRESH_PREFIX: &str = "!lazy_op_";

/// The outcome of [`solve_lazy_bv_abstraction`], with refinement telemetry that
/// quantifies how much bit-blasting the abstraction avoided.
#[derive(Debug)]
pub struct LazyBvOutcome {
    /// The decision (every `sat` already replayed against the original query).
    pub result: CheckResult,
    /// Distinct heavy operations (`bvmul`/`bvudiv`/…) found in the query.
    pub ops_total: usize,
    /// How many of them had to be refined (exactly bit-blasted). `0` means the
    /// verdict was reached without materializing a single heavy gadget.
    pub ops_refined: usize,
    /// Abstraction-refinement rounds taken.
    pub rounds: usize,
}

/// Decides `assertions` with the lazy abstraction-refinement strategy, returning
/// only the [`CheckResult`].
///
/// # Errors
///
/// Returns [`SolverError`] from the eager sub-solver or on a replay soundness
/// alarm.
pub fn check_lazy_bv_abstraction(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    Ok(solve_lazy_bv_abstraction(arena, assertions, config)?.result)
}

/// Read-only variant of [`solve_lazy_bv_abstraction`]: decides `assertions`
/// without mutating the caller's arena, so it fits the `&TermArena` consumers
/// (the [`crate::SolverBackend`] trait, the bench pipeline) that cannot hand out
/// a `&mut` arena.
///
/// The strategy needs to declare fresh abstraction symbols, so this runs it on a
/// disposable [`TermArena::clone`] (an identical arena where the input
/// `TermId`s/`SymbolId`s stay valid). The returned model is already restricted
/// to the original (non-`!lazy_op_*`) symbols, so it replays against the caller's
/// arena unchanged. Sound for the same reasons as the mutable version:
/// over-approximation for `unsat`, replay-checked `sat`.
///
/// # Errors
///
/// Returns [`SolverError`] from the eager sub-solver or on a replay soundness
/// alarm.
pub fn check_lazy_bv_abstraction_ro(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<LazyBvOutcome, SolverError> {
    let mut scratch = arena.clone();
    solve_lazy_bv_abstraction(&mut scratch, assertions, config)
}

/// Decides `assertions` with the lazy abstraction-refinement strategy, returning
/// the full [`LazyBvOutcome`] (verdict + telemetry).
///
/// # Errors
///
/// Returns [`SolverError`] from the eager sub-solver or on a replay soundness
/// alarm.
pub fn solve_lazy_bv_abstraction(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<LazyBvOutcome, SolverError> {
    let ops = collect_heavy_ops(arena, assertions);
    if ops.is_empty() {
        // Nothing to abstract; the eager strategy is already minimal here.
        let result = solve(arena, assertions, config)?;
        return Ok(LazyBvOutcome {
            result,
            ops_total: 0,
            ops_refined: 0,
            rounds: 1,
        });
    }

    // Fresh variable per heavy op; `replacements` maps each op term to its
    // abstraction variable, `fresh_sym` remembers the symbol for model lookups.
    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    let mut fresh_sym: HashMap<TermId, axeyum_ir::SymbolId> = HashMap::new();
    for (i, &op_term) in ops.iter().enumerate() {
        let sort = arena.sort_of(op_term);
        let sym = arena.declare(&format!("{FRESH_PREFIX}{i}"), sort)?;
        let var = arena.var(sym);
        replacements.insert(op_term, var);
        fresh_sym.insert(op_term, sym);
    }

    // Abstracted assertions (every heavy op replaced by its fresh variable).
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut abstracted = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        abstracted.push(replace_subterms(
            arena,
            assertion,
            &replacements,
            &mut memo,
        )?);
    }

    let mut refined: HashSet<TermId> = HashSet::new();
    let max_rounds = ops.len() + 1;
    for round in 1..=max_rounds {
        let constraints = round_constraints(arena, &abstracted, &ops, &refined, &replacements)?;
        match solve(arena, &constraints, config)? {
            CheckResult::Unsat => {
                return Ok(outcome(CheckResult::Unsat, &ops, &refined, round));
            }
            CheckResult::Unknown(reason) => {
                return Ok(outcome(CheckResult::Unknown(reason), &ops, &refined, round));
            }
            CheckResult::Sat(model) => {
                let assignment = model.to_assignment();
                if replay_holds(arena, assertions, &assignment)? {
                    let restricted = restrict_model(arena, &model);
                    return Ok(outcome(CheckResult::Sat(restricted), &ops, &refined, round));
                }
                // Spurious: refine every unrefined op whose abstraction value
                // disagrees with its real result under this model.
                let mut progressed = false;
                for &op_term in &ops {
                    if refined.contains(&op_term) {
                        continue;
                    }
                    let fresh_value = model.get(fresh_sym[&op_term]);
                    let real_value = eval(arena, op_term, &assignment)?;
                    if fresh_value.as_ref() != Some(&real_value) {
                        refined.insert(op_term);
                        progressed = true;
                    }
                }
                if !progressed {
                    return Err(SolverError::Backend(
                        "lazy-bv: original replay failed but every heavy op was \
                         consistent with its abstraction (soundness bug)"
                            .to_string(),
                    ));
                }
            }
        }
    }

    // Unreachable in principle (after all ops refine the problem is exact), but
    // bounded for safety: report `unknown`, never a wrong verdict.
    Ok(outcome(
        CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!("lazy-bv abstraction exceeded {max_rounds} refinement rounds"),
        }),
        &ops,
        &refined,
        max_rounds,
    ))
}

fn outcome(
    result: CheckResult,
    ops: &[TermId],
    refined: &HashSet<TermId>,
    rounds: usize,
) -> LazyBvOutcome {
    LazyBvOutcome {
        result,
        ops_total: ops.len(),
        ops_refined: refined.len(),
        rounds,
    }
}

/// The eager problem for one refinement round: the abstraction plus the exact
/// `fresh == op(lhs, rhs)` definition of every already-refined heavy op.
fn round_constraints(
    arena: &mut TermArena,
    abstracted: &[TermId],
    ops: &[TermId],
    refined: &HashSet<TermId>,
    replacements: &HashMap<TermId, TermId>,
) -> Result<Vec<TermId>, SolverError> {
    let mut constraints = abstracted.to_vec();
    for &op_term in ops {
        if !refined.contains(&op_term) {
            continue;
        }
        let (op, lhs, rhs) = operands(arena, op_term);
        let mut rmemo: HashMap<TermId, TermId> = HashMap::new();
        let abs_lhs = replace_subterms(arena, lhs, replacements, &mut rmemo)?;
        let abs_rhs = replace_subterms(arena, rhs, replacements, &mut rmemo)?;
        let exact = rebuild_binary(arena, op, abs_lhs, abs_rhs)?;
        let fresh = replacements[&op_term];
        constraints.push(arena.eq(fresh, exact)?);
    }
    Ok(constraints)
}

/// Whether `op` is a heavy gadget worth abstracting.
fn is_heavy(op: Op) -> bool {
    matches!(
        op,
        Op::BvMul | Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod
    )
}

/// Whether `assertions` contain any heavy gadget (`bvmul`/`bvudiv`/…) — the
/// signal the [`crate::Strategy::Auto`] selector uses to prefer the low-memory
/// abstraction strategy.
pub(crate) fn has_heavy_ops(arena: &TermArena, assertions: &[TermId]) -> bool {
    !collect_heavy_ops(arena, assertions).is_empty()
}

/// Distinct heavy-op subterms in `assertions`, in deterministic first-seen order.
fn collect_heavy_ops(arena: &TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut ops = Vec::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if is_heavy(*op) {
                ops.push(term);
            }
            for &arg in args.iter().rev() {
                stack.push(arg);
            }
        }
    }
    ops
}

/// The operator and two operands of an abstractable heavy-op term.
fn operands(arena: &TermArena, term: TermId) -> (Op, TermId, TermId) {
    match arena.node(term) {
        TermNode::App { op, args } if is_heavy(*op) => (*op, args[0], args[1]),
        _ => unreachable!("operands called on a non-heavy term"),
    }
}

/// Rebuilds the exact heavy operation over (possibly abstracted) operands.
fn rebuild_binary(
    arena: &mut TermArena,
    op: Op,
    lhs: TermId,
    rhs: TermId,
) -> Result<TermId, SolverError> {
    let result = match op {
        Op::BvMul => arena.bv_mul(lhs, rhs)?,
        Op::BvUdiv => arena.bv_udiv(lhs, rhs)?,
        Op::BvUrem => arena.bv_urem(lhs, rhs)?,
        Op::BvSdiv => arena.bv_sdiv(lhs, rhs)?,
        Op::BvSrem => arena.bv_srem(lhs, rhs)?,
        Op::BvSmod => arena.bv_smod(lhs, rhs)?,
        _ => unreachable!("rebuild_binary called on a non-heavy op"),
    };
    Ok(result)
}

/// Whether every assertion evaluates to `true` under `assignment`.
fn replay_holds(
    arena: &TermArena,
    assertions: &[TermId],
    assignment: &axeyum_ir::Assignment,
) -> Result<bool, SolverError> {
    for &assertion in assertions {
        if eval(arena, assertion, assignment)? != Value::Bool(true) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Copies `model` without the internal `!lazy_op_*` abstraction variables.
fn restrict_model(arena: &TermArena, model: &Model) -> Model {
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with(FRESH_PREFIX) {
            continue;
        }
        if let Some(value) = model.get(symbol) {
            out.set(symbol, value);
        }
    }
    for (func, value) in model.functions() {
        out.set_function(func, value.clone());
    }
    out
}
