//! Bounded model checking — reachability over a symbolic transition system.
//!
//! This is the reachability-analysis consumer the symbolic-execution primitives
//! were built for. A [`TransitionSystem`] describes a state machine symbolically
//! (state variables, an initial-state predicate, a transition relation, and a
//! "bad"/property-violation predicate). [`bounded_model_check`] unrolls it up to
//! a bound `k` and asks, at each depth, *can a bad state be reached in exactly
//! this many transitions?*
//!
//! It rides the warm [`IncrementalBvSolver`]: `init` and each `trans` step are
//! asserted once into the persistent CNF (shared subterms encode once, learned
//! clauses are kept across depths), and each depth's `bad` query is a
//! `push`/`check`/`pop` over that warm state.
//!
//! Soundness follows the project invariant exactly:
//!
//! * [`BmcOutcome::Reachable`] carries a **replay-checked** counterexample trace
//!   — the incremental solver already evaluated the model against every active
//!   assertion (`init`, the `trans` chain, and `bad`) with the ground evaluator
//!   before returning it. It is a genuine witnessed path to a bad state.
//! * [`BmcOutcome::UnreachableWithinBound`] is a **bounded** statement only: no
//!   bad state is reachable in `≤ bound` transitions. It is deliberately *not* a
//!   proof of unreachability — that needs k-induction or interpolation (a
//!   future-work lever toward unbounded safety, see PLAN.md Track C1).
//! * [`BmcOutcome::Unknown`] is first-class: a resource limit or an unsupported
//!   construct at some depth is reported honestly, never as a safe result.
//!
//! The first slice rides the array-free warm path (BV/Bool transition systems);
//! symbolic-memory transition relations are the ADR-0030 follow-up.

use axeyum_ir::{SymbolId, TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownReason};
use crate::incremental::IncrementalBvSolver;
use crate::model::Model;

/// A symbolic transition system: the input to [`bounded_model_check`].
///
/// All formulas are built over **state variable symbols**, freshly declared per
/// time step via [`state_vars`](TransitionSystem::state_vars) so that distinct
/// steps get distinct variables (the unrolling). Every step must declare the
/// same number of variables with the same sorts, in the same order.
pub trait TransitionSystem {
    /// Declares (or returns) the state variable symbols for time `step`.
    ///
    /// Implementations typically `arena.declare(&format!("{name}@{step}"), sort)`
    /// one symbol per state component. The returned arity/sorts must not vary
    /// with `step`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if a declaration fails.
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError>;

    /// The initial-state constraint, over the step-0 variables `s0`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the predicate cannot be built.
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError>;

    /// The transition relation from `pre` (step `k`) to `post` (step `k+1`).
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the relation cannot be built.
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError>;

    /// The "bad"/property-violation predicate over a state `s`. A bad state is
    /// the target of the reachability query.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the predicate cannot be built.
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError>;
}

/// The result of [`bounded_model_check`].
#[derive(Debug, Clone)]
pub enum BmcOutcome {
    /// A bad state is reachable in exactly `steps` transitions (`steps == 0`
    /// means the initial state itself is bad). `model` is the replay-checked
    /// counterexample: it assigns every step variable along the witnessing path.
    Reachable {
        /// The number of transitions to the bad state.
        steps: usize,
        /// The witnessed trace (assignments to all unrolled state variables).
        model: Model,
    },
    /// No bad state is reachable within `bound` transitions. A **bounded**
    /// guarantee, not a proof of unreachability.
    UnreachableWithinBound {
        /// The depth searched (inclusive).
        bound: usize,
    },
    /// The reachability query at depth `steps` could not be decided.
    Unknown {
        /// The depth whose query was undecided.
        steps: usize,
        /// The classified reason.
        reason: UnknownReason,
    },
}

/// Bounded model checking: is a bad state of `system` reachable within `bound`
/// transitions?
///
/// Unrolls `system` depth by depth over a warm [`IncrementalBvSolver`]. At depth
/// `k` the active assertions are `init(s0) ∧ trans(s0,s1) ∧ … ∧ trans(s_{k-1},s_k)`
/// and the query (under a temporary scope) is `bad(s_k)`; a `sat` there is a
/// length-`k` counterexample. The base assertions are warm — each `trans` step is
/// added once, so depth `k+1` reuses everything depth `k` already encoded.
///
/// Returns at the **shallowest** depth a bad state is reachable, or
/// [`BmcOutcome::UnreachableWithinBound`] if none is found through `bound`.
///
/// # Errors
///
/// Returns [`SolverError`] if building the system's terms or driving the warm
/// solver fails. A solver *timeout/unsupported* at some depth is not an error —
/// it is reported as [`BmcOutcome::Unknown`].
pub fn bounded_model_check(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    bound: usize,
    config: &SolverConfig,
) -> Result<BmcOutcome, SolverError> {
    let mut solver = IncrementalBvSolver::with_config(config.clone());

    // Step 0: declare s0 and pin the initial-state constraint permanently.
    let s0 = system.state_vars(arena, 0)?;
    let init = system.init(arena, &s0)?;
    solver.assert(arena, init)?;

    let mut states: Vec<Vec<SymbolId>> = vec![s0];

    for k in 0..=bound {
        // Query: is bad(s_k) reachable given init and the trans chain so far?
        // Push a temporary scope so the bad assertion is dropped after the check.
        let bad = system.bad(arena, &states[k])?;
        solver.push()?;
        solver.assert(arena, bad)?;
        let result = solver.check(arena)?;
        solver.pop();

        match result {
            CheckResult::Sat(model) => {
                return Ok(BmcOutcome::Reachable { steps: k, model });
            }
            CheckResult::Unknown(reason) => {
                return Ok(BmcOutcome::Unknown { steps: k, reason });
            }
            CheckResult::Unsat => {}
        }

        // Extend the unrolling by one transition (unless this was the last depth).
        if k < bound {
            let next = system.state_vars(arena, k + 1)?;
            let trans = system.trans(arena, &states[k], &next)?;
            solver.assert(arena, trans)?;
            states.push(next);
        }
    }

    Ok(BmcOutcome::UnreachableWithinBound { bound })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Sort, Value};

    /// An 8-bit counter: `x@0 = start`, `x@{k+1} = x@k + 1`, bad when `x = target`.
    struct Counter {
        start: u128,
        target: u128,
    }

    fn counter_var(arena: &mut TermArena, step: usize) -> SymbolId {
        arena
            .declare(&format!("x@{step}"), Sort::BitVec(8))
            .unwrap()
    }

    impl TransitionSystem for Counter {
        fn state_vars(
            &self,
            arena: &mut TermArena,
            step: usize,
        ) -> Result<Vec<SymbolId>, SolverError> {
            Ok(vec![counter_var(arena, step)])
        }

        fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
            let x = arena.var(s0[0]);
            let c = arena.bv_const(8, self.start)?;
            Ok(arena.eq(x, c)?)
        }

        fn trans(
            &self,
            arena: &mut TermArena,
            pre: &[SymbolId],
            post: &[SymbolId],
        ) -> Result<TermId, SolverError> {
            let x = arena.var(pre[0]);
            let one = arena.bv_const(8, 1)?;
            let inc = arena.bv_add(x, one)?;
            let x_next = arena.var(post[0]);
            Ok(arena.eq(x_next, inc)?)
        }

        fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
            let x = arena.var(s[0]);
            let c = arena.bv_const(8, self.target)?;
            Ok(arena.eq(x, c)?)
        }
    }

    #[test]
    fn reachable_counter_finds_shallowest_depth() {
        let mut arena = TermArena::new();
        let system = Counter {
            start: 0,
            target: 5,
        };
        let outcome =
            bounded_model_check(&mut arena, &system, 10, &SolverConfig::default()).unwrap();
        match outcome {
            BmcOutcome::Reachable { steps, model } => {
                assert_eq!(steps, 5, "0 → 5 takes exactly five increments");
                // The counterexample trace is a genuine, replay-checked path.
                for k in 0..=5u128 {
                    let sym = arena.find_symbol(&format!("x@{k}")).unwrap();
                    assert_eq!(
                        model.get(sym),
                        Some(Value::Bv { width: 8, value: k }),
                        "trace value at step {k}"
                    );
                }
            }
            other => panic!("expected Reachable, got {other:?}"),
        }
    }

    #[test]
    fn reachable_at_step_zero_when_init_is_bad() {
        let mut arena = TermArena::new();
        let system = Counter {
            start: 7,
            target: 7,
        };
        let outcome =
            bounded_model_check(&mut arena, &system, 4, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, BmcOutcome::Reachable { steps: 0, .. }),
            "init state already bad ⇒ reachable in 0 transitions, got {outcome:?}"
        );
    }

    #[test]
    fn unreachable_within_bound_is_honest_and_bounded() {
        let mut arena = TermArena::new();
        // 0,1,2,3 in four steps never reaches 200.
        let system = Counter {
            start: 0,
            target: 200,
        };
        let outcome =
            bounded_model_check(&mut arena, &system, 3, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, BmcOutcome::UnreachableWithinBound { bound: 3 }),
            "200 is unreachable within 3 increments from 0, got {outcome:?}"
        );
    }

    #[test]
    fn deeper_bound_eventually_reaches_a_wrapping_target() {
        // The counter wraps mod 256; target 250 is reachable from 248 in 2 steps.
        let mut arena = TermArena::new();
        let system = Counter {
            start: 248,
            target: 250,
        };
        let outcome =
            bounded_model_check(&mut arena, &system, 8, &SolverConfig::default()).unwrap();
        assert!(
            matches!(outcome, BmcOutcome::Reachable { steps: 2, .. }),
            "248 → 250 is two increments, got {outcome:?}"
        );
    }
}
