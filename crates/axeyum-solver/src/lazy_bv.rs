//! Low-memory lazy-multiplier abstraction-refinement BV strategy (ADR-0019).
//!
//! The eager bit-blaster's memory is dominated by multiplier circuits (measured
//! ~1.2k–2.5k AIG AND-nodes for a single width-16/24 `bvmul`). This strategy
//! avoids materializing them unless they matter:
//!
//! 1. **Abstract** every `bvmul` subterm by a fresh, unconstrained variable of
//!    the same sort. Dropping the product constraint *enlarges* the solution set,
//!    so the abstraction is a sound **over-approximation**.
//! 2. **Solve** the (much smaller) abstraction with the eager pure-Rust path.
//!    - `unsat` ⇒ the original is `unsat` (over-approximation), with **no
//!      multiplier ever bit-blasted**.
//!    - `sat` ⇒ **replay** the original assertions under the model. If they hold,
//!      it is a genuine model. Otherwise the abstraction exploited a fresh
//!      variable whose value differs from the real product: **refine** those
//!      multipliers by adding their exact `fresh == lhs * rhs` constraint
//!      (bit-blasting only those), and re-solve.
//!
//! Refinement only ever adds multipliers, so after at most one round per `bvmul`
//! the problem is fully precise (equivalent to the eager strategy): the loop is
//! **sound and complete and terminating**, with memory ≤ eager and often far
//! less. Every `sat` is replayed (the trust anchor); `unsat` is sound by the
//! over-approximation argument and cross-checked against the eager strategy in
//! tests.
//!
//! Only `bvmul` is abstracted today; division/remainder (the other heavy
//! gadgets) are the natural next extension.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Op, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::replace_subterms;

use crate::auto::solve;
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

const FRESH_PREFIX: &str = "!lazy_mul_";

/// The outcome of [`solve_lazy_bv_abstraction`], with refinement telemetry that
/// quantifies how much bit-blasting the abstraction avoided.
#[derive(Debug)]
pub struct LazyBvOutcome {
    /// The decision (every `sat` already replayed against the original query).
    pub result: CheckResult,
    /// Distinct `bvmul` subterms found in the query.
    pub muls_total: usize,
    /// How many of them had to be refined (exactly bit-blasted). `0` means the
    /// verdict was reached without materializing a single multiplier.
    pub muls_refined: usize,
    /// Abstraction-refinement rounds taken.
    pub rounds: usize,
}

/// Decides `assertions` with the lazy-multiplier abstraction-refinement
/// strategy, returning only the [`CheckResult`].
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

/// Decides `assertions` with the lazy-multiplier abstraction-refinement
/// strategy, returning the full [`LazyBvOutcome`] (verdict + telemetry).
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
    let muls = collect_muls(arena, assertions);
    if muls.is_empty() {
        // Nothing to abstract; the eager strategy is already minimal here.
        let result = solve(arena, assertions, config)?;
        return Ok(LazyBvOutcome {
            result,
            muls_total: 0,
            muls_refined: 0,
            rounds: 1,
        });
    }

    // Fresh variable per multiplier; `replacements` maps each `bvmul` term to its
    // abstraction variable, `fresh_sym` remembers the symbol for model lookups.
    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    let mut fresh_sym: HashMap<TermId, axeyum_ir::SymbolId> = HashMap::new();
    for (i, &mul) in muls.iter().enumerate() {
        let sort = arena.sort_of(mul);
        let sym = arena.declare(&format!("{FRESH_PREFIX}{i}"), sort)?;
        let var = arena.var(sym);
        replacements.insert(mul, var);
        fresh_sym.insert(mul, sym);
    }

    // Abstracted assertions (every `bvmul` replaced by its fresh variable).
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
    let max_rounds = muls.len() + 1;
    for round in 1..=max_rounds {
        let constraints = round_constraints(arena, &abstracted, &muls, &refined, &replacements)?;
        match solve(arena, &constraints, config)? {
            CheckResult::Unsat => {
                return Ok(LazyBvOutcome {
                    result: CheckResult::Unsat,
                    muls_total: muls.len(),
                    muls_refined: refined.len(),
                    rounds: round,
                });
            }
            CheckResult::Unknown(reason) => {
                return Ok(LazyBvOutcome {
                    result: CheckResult::Unknown(reason),
                    muls_total: muls.len(),
                    muls_refined: refined.len(),
                    rounds: round,
                });
            }
            CheckResult::Sat(model) => {
                let assignment = model.to_assignment();
                if replay_holds(arena, assertions, &assignment)? {
                    return Ok(LazyBvOutcome {
                        result: CheckResult::Sat(restrict_model(arena, &model)),
                        muls_total: muls.len(),
                        muls_refined: refined.len(),
                        rounds: round,
                    });
                }
                // Spurious: refine every unrefined mul whose abstraction value
                // disagrees with its real product under this model.
                let mut progressed = false;
                for &mul in &muls {
                    if refined.contains(&mul) {
                        continue;
                    }
                    let fresh_value = model.get(fresh_sym[&mul]);
                    let real_value = eval(arena, mul, &assignment)?;
                    if fresh_value.as_ref() != Some(&real_value) {
                        refined.insert(mul);
                        progressed = true;
                    }
                }
                if !progressed {
                    return Err(SolverError::Backend(
                        "lazy-bv: original replay failed but every multiplier was \
                         consistent with its abstraction (soundness bug)"
                            .to_string(),
                    ));
                }
            }
        }
    }

    // Unreachable in principle (after all muls refine the problem is exact), but
    // bounded for safety: report `unknown`, never a wrong verdict.
    Ok(LazyBvOutcome {
        result: CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!("lazy-bv abstraction exceeded {max_rounds} refinement rounds"),
        }),
        muls_total: muls.len(),
        muls_refined: refined.len(),
        rounds: max_rounds,
    })
}

/// The eager problem for one refinement round: the abstraction plus the exact
/// `fresh == lhs * rhs` definition of every already-refined multiplier.
fn round_constraints(
    arena: &mut TermArena,
    abstracted: &[TermId],
    muls: &[TermId],
    refined: &HashSet<TermId>,
    replacements: &HashMap<TermId, TermId>,
) -> Result<Vec<TermId>, SolverError> {
    let mut constraints = abstracted.to_vec();
    for &mul in muls {
        if !refined.contains(&mul) {
            continue;
        }
        let (lhs, rhs) = mul_children(arena, mul);
        let mut rmemo: HashMap<TermId, TermId> = HashMap::new();
        let abs_lhs = replace_subterms(arena, lhs, replacements, &mut rmemo)?;
        let abs_rhs = replace_subterms(arena, rhs, replacements, &mut rmemo)?;
        let product = arena.bv_mul(abs_lhs, abs_rhs)?;
        let fresh = replacements[&mul];
        constraints.push(arena.eq(fresh, product)?);
    }
    Ok(constraints)
}

/// Distinct `bvmul` subterms in `assertions`, in deterministic first-seen order.
fn collect_muls(arena: &TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut muls = Vec::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if *op == Op::BvMul {
                muls.push(term);
            }
            for &arg in args.iter().rev() {
                stack.push(arg);
            }
        }
    }
    muls
}

/// The two operands of a `bvmul` term.
fn mul_children(arena: &TermArena, mul: TermId) -> (TermId, TermId) {
    match arena.node(mul) {
        TermNode::App {
            op: Op::BvMul,
            args,
        } => (args[0], args[1]),
        _ => unreachable!("mul_children called on a non-bvmul term"),
    }
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

/// Copies `model` without the internal `!lazy_mul_*` abstraction variables.
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
