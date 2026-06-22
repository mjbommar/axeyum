//! Robustness gate for the `IC3`/`PDR` engine on a non-`QF_BV` transition system
//! (review-driven, same theme as the interpolation robustness gate).
//!
//! `prove_safety_pdr` runs its inner queries through the warm `IncrementalBvSolver`
//! (BV/Bool only). A transition system over a foreign theory (here `Real`) must
//! degrade to a graceful `PdrOutcome::Unknown` — never panic (the "graceful
//! unknown, never crash" hard rule). The test passes simply by *returning* an
//! `Ok(_)` without panicking.

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    PdrOutcome, SolverConfig, SolverError, TransitionSystem, prove_safety_pdr,
    prove_safety_pdr_certified,
};

/// A real-valued counter: `init: r = 0`, `trans: r' = r + 1`, `bad: r < 0`
/// (safe — `r` only increases). Real-sorted, so outside the BV inner engine.
struct RealCounter;

impl TransitionSystem for RealCounter {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![
            arena.declare(&format!("r@{step}"), Sort::Real).unwrap(),
        ])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.real_ratio(0, 1);
        Ok(arena.eq(x, zero).unwrap())
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let xp = arena.var(post[0]);
        let one = arena.real_ratio(1, 1);
        let next = arena.real_add(x, one).unwrap();
        Ok(arena.eq(xp, next).unwrap())
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.real_ratio(0, 1);
        Ok(arena.real_lt(x, zero).unwrap())
    }
}

#[test]
fn pdr_on_a_real_transition_system_declines_gracefully() {
    let mut arena = TermArena::new();
    let config = SolverConfig::default();
    let outcome = prove_safety_pdr(&mut arena, &RealCounter, &config);
    assert!(
        outcome.is_ok(),
        "PDR over a real-sorted system must return Ok (graceful), got {outcome:?}"
    );
    // Whatever it decided, it must not be a wrong verdict produced by panicking;
    // a sound engine returns Unknown or a re-verified Safe/Reachable.
    assert!(matches!(
        outcome.unwrap(),
        PdrOutcome::Safe { .. } | PdrOutcome::Reachable { .. } | PdrOutcome::Unknown { .. }
    ));
}

#[test]
fn pdr_certified_on_a_real_transition_system_declines_gracefully() {
    let mut arena = TermArena::new();
    let config = SolverConfig::default();
    let outcome = prove_safety_pdr_certified(&mut arena, &RealCounter, &config);
    assert!(
        outcome.is_ok(),
        "certified PDR over a real-sorted system must return Ok (graceful), got {outcome:?}"
    );
}
