//! A CFG → [`TransitionSystem`] adapter for `while`-loop verification via the
//! solver's bounded model checker.
//!
//! Phase 1 (and the [`crate::lower`] `While` path) bounded-checks a loop by
//! **unrolling** it into the one-shot `prove` query — sound, certifiable, and the
//! default for `#[verify]`. This module wires the *other* route the PLAN names: a
//! [`TransitionSystem`] driven by [`bounded_model_check`], which keeps the warm
//! incremental solver hot across unroll depths (each `trans` step is asserted
//! once and reused). It is the architecture that scales to deeper bounds.
//!
//! ## Fragment / U6 note
//!
//! [`bounded_model_check`] rides the **array-free** warm path (BV/Bool state);
//! [`bounded_model_check_with_memory`] adds array state but decides each depth
//! **one-shot** via the validated eager read-over-write + Ackermann elimination
//! (it does *not* use the warm array path that `UPSTREAM-FEEDBACK` U6 reports as
//! refused). So a `while` over **scalar register/BV state** — what this adapter
//! targets — is fully in fragment and not U6-blocked. A loop whose state is a
//! symbolic-memory array would route through the one-shot memory path; that is a
//! follow-up (and, per U6, must avoid the warm array path).
//!
//! ## Soundness
//!
//! A [`LoopSafety::BugReachable`] result carries the solver's replay-checked
//! counterexample model — a genuine witnessed path to a bad state.
//! [`LoopSafety::SafeWithinBound`] is a **bounded** guarantee (no bad state in
//! `≤ bound` iterations), never a total-correctness claim. [`LoopSafety::Unknown`]
//! is first-class.
//!
//! [`bounded_model_check_with_memory`]: axeyum_solver::bounded_model_check_with_memory

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    BmcOutcome, Model, SolverConfig, SolverError, TransitionSystem, bounded_model_check,
};

use crate::ast::Ty;

/// The outcome of a BMC loop check.
#[derive(Debug, Clone)]
pub enum LoopSafety {
    /// No bad state reachable within `bound` loop iterations (a bounded guarantee).
    SafeWithinBound {
        /// The unroll depth searched (inclusive).
        bound: usize,
    },
    /// A bad state is reachable in `steps` iterations; `model` is the
    /// replay-checked witnessing trace over the unrolled state variables.
    BugReachable {
        /// Iterations to the bad state.
        steps: usize,
        /// The witnessed trace.
        model: Model,
    },
    /// Undecided at some depth (resource limit / out-of-fragment), reported
    /// honestly — never a wrong `Safe`.
    Unknown {
        /// A human-readable reason.
        reason: String,
    },
}

/// A `TransitionSystem` for a counter loop `while i < limit { i = i + 1; }` whose
/// **bad state** is `i == bad_value` becoming reachable — the canonical
/// data-dependent `while` shape (a loop counter advancing past a forbidden
/// value). State is the pair `(i, limit)` of `width`-bit unsigned BVs; `limit`
/// is a symbolic input held constant by the transition relation, so the BMC
/// search ranges over all `limit` values.
///
/// This is the worked adapter demonstrating the [`bounded_model_check`] route is
/// usable for scalar-state loops (not blocked by `UPSTREAM-FEEDBACK` U6); a fully
/// general CFG→`TransitionSystem` lowering from arbitrary `#[verify]` bodies is a
/// recorded follow-up (the unrolling path in [`crate::lower`] covers the general
/// case today).
pub struct CounterLoopSystem {
    /// BV width of the counter and limit.
    pub width: u32,
    /// The forbidden value the loop must not let `i` reach.
    pub bad_value: u128,
}

impl CounterLoopSystem {
    /// A counter-loop system over `u<width>` with forbidden value `bad_value`.
    #[must_use]
    pub fn new(ty: Ty, bad_value: u128) -> Option<Self> {
        let width = ty.width()?;
        Some(CounterLoopSystem { width, bad_value })
    }
}

impl TransitionSystem for CounterLoopSystem {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        let i = arena.declare(&format!("i@{step}"), Sort::BitVec(self.width))?;
        let limit = arena.declare(&format!("limit@{step}"), Sort::BitVec(self.width))?;
        Ok(vec![i, limit])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        // i starts at 0; limit is an unconstrained symbolic input.
        let i0 = arena.var(s0[0]);
        let zero = arena.bv_const(self.width, 0)?;
        Ok(arena.eq(i0, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let (i, limit) = (arena.var(pre[0]), arena.var(pre[1]));
        let (i_next, limit_next) = (arena.var(post[0]), arena.var(post[1]));
        // Guard `i < limit`: when it holds, `i' = i + 1`; otherwise `i' = i`
        // (the loop has exited and the state is a stutter — keeps the bad-state
        // query meaningful at every depth). `limit` is invariant.
        let guard = arena.bv_ult(i, limit)?;
        let one = arena.bv_const(self.width, 1)?;
        let inc = arena.bv_add(i, one)?;
        let i_step = arena.ite(guard, inc, i)?;
        let i_ok = arena.eq(i_next, i_step)?;
        let limit_ok = arena.eq(limit_next, limit)?;
        Ok(arena.and(i_ok, limit_ok)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        // The bad state: the counter has reached the forbidden value.
        let i = arena.var(s[0]);
        let bad = arena.bv_const(self.width, self.bad_value)?;
        Ok(arena.eq(i, bad)?)
    }
}

/// A relation over the loop state, built from the pre-state variable terms.
type LoopRel = Box<dyn Fn(&mut TermArena, &[TermId]) -> Result<TermId, SolverError>>;
/// The per-variable next-value relation (one term per state variable).
type LoopUpdate = Box<dyn Fn(&mut TermArena, &[TermId]) -> Result<Vec<TermId>, SolverError>>;

/// A general bounded-loop [`TransitionSystem`] over **N scalar BV state variables**
/// (C4.1), built from caller-supplied `init`/`guard`/`update`/`bad` relations
/// rather than a single fixed loop shape. It generalizes [`CounterLoopSystem`]: a
/// straight-line scalar loop body lowers to an `update` closure producing each
/// variable's next value, and `trans` becomes `guard ? update : stutter` per
/// variable. (The AST→closure lowering is C4.3; this is the reusable engine.)
pub struct ScalarLoopSystem {
    width: u32,
    names: Vec<&'static str>,
    init: LoopRel,
    guard: LoopRel,
    update: LoopUpdate,
    bad: LoopRel,
}

impl ScalarLoopSystem {
    /// Builds an N-variable scalar loop system. `names` labels the state vars (one
    /// per loop variable); the relations receive the pre-state variable terms in
    /// the same order. `update` must return exactly `names.len()` next-value terms.
    #[must_use]
    pub fn new(
        width: u32,
        names: Vec<&'static str>,
        init: LoopRel,
        guard: LoopRel,
        update: LoopUpdate,
        bad: LoopRel,
    ) -> Self {
        Self {
            width,
            names,
            init,
            guard,
            update,
            bad,
        }
    }

    fn vars(arena: &mut TermArena, syms: &[SymbolId]) -> Vec<TermId> {
        syms.iter().map(|&s| arena.var(s)).collect()
    }
}

impl TransitionSystem for ScalarLoopSystem {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        self.names
            .iter()
            .map(|n| {
                arena
                    .declare(&format!("{n}@{step}"), Sort::BitVec(self.width))
                    .map_err(Into::into)
            })
            .collect()
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let vars = Self::vars(arena, s0);
        (self.init)(arena, &vars)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let pre_t = Self::vars(arena, pre);
        let post_t = Self::vars(arena, post);
        let guard = (self.guard)(arena, &pre_t)?;
        let updated = (self.update)(arena, &pre_t)?;
        // Each variable advances by its update under the guard, else stutters.
        let mut acc: Option<TermId> = None;
        for (k, &post_k) in post_t.iter().enumerate() {
            let step_val = arena.ite(guard, updated[k], pre_t[k])?;
            let eq_k = arena.eq(post_k, step_val)?;
            acc = Some(match acc {
                None => eq_k,
                Some(a) => arena.and(a, eq_k)?,
            });
        }
        acc.ok_or_else(|| {
            SolverError::from(axeyum_ir::IrError::SortMismatch {
                expected: "at least one loop state variable",
                found: Sort::Bool,
            })
        })
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let vars = Self::vars(arena, s);
        (self.bad)(arena, &vars)
    }
}

/// Runs [`bounded_model_check`] on `system` up to `bound` iterations and maps the
/// outcome to a [`LoopSafety`].
///
/// # Errors
///
/// Returns a [`SolverError`] only on a hard engine failure; an undecided depth is
/// a [`LoopSafety::Unknown`], not an error.
pub fn check_loop(
    system: &CounterLoopSystem,
    bound: usize,
    config: &SolverConfig,
) -> Result<LoopSafety, SolverError> {
    run_loop(system, bound, config)
}

/// Runs [`bounded_model_check`] on any [`TransitionSystem`] and maps the outcome
/// to a [`LoopSafety`] — the generic driver behind [`check_loop`] and the
/// [`ScalarLoopSystem`] route.
///
/// # Errors
///
/// As [`check_loop`].
pub fn run_loop(
    system: &impl TransitionSystem,
    bound: usize,
    config: &SolverConfig,
) -> Result<LoopSafety, SolverError> {
    let mut arena = TermArena::new();
    let outcome = bounded_model_check(&mut arena, system, bound, config)?;
    Ok(match outcome {
        BmcOutcome::Reachable { steps, model } => LoopSafety::BugReachable { steps, model },
        BmcOutcome::UnreachableWithinBound { bound } => LoopSafety::SafeWithinBound { bound },
        BmcOutcome::Unknown { steps, reason } => LoopSafety::Unknown {
            reason: format!("undecided at depth {steps}: {reason:?}"),
        },
    })
}
