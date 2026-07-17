//! Integration tests for the `McMillan` interpolation-based model-checking (`IMC`)
//! engine.
//!
//! The soundness theme runs through every test: a `Safe` verdict is never trusted
//! on the engine's say-so — each safe test **independently re-checks** the returned
//! invariant's three implication conditions (initiation, consecution, safety) with
//! [`check_auto`], and the `Reachable` test cross-checks against
//! [`bounded_model_check`]. A wrong `Safe`/`Reachable` would fail these independent
//! checks; an over-eager `Unknown` is acceptable.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    BmcOutcome, CheckResult, ImcOutcome, SafetyOutcome, SolverConfig, SolverError,
    TransitionSystem, bounded_model_check, check_auto, prove_safety_imc, prove_safety_k_induction,
};
use std::time::Duration;

/// A width-8 counter **stuck at 0**: `init: x = 0`, `trans: x' = ite(x == 0, 0,
/// x + 1)`. The only reachable state is `x = 0`. `bad: x == target`. For a
/// `target` in `1..` this is *safe* but **not** k-inductive for any small `k`
/// (from the unreachable-but-good state `x = target-1` the transition steps
/// straight into bad). The real inductive invariant is `x ∉ {1,…,target}`, which
/// `IMC` must discover by interpolation.
struct StuckCounter {
    target: u128,
}

fn counter_var(arena: &mut TermArena, step: usize) -> SymbolId {
    arena
        .declare(&format!("x@{step}"), Sort::BitVec(8))
        .unwrap()
}

impl TransitionSystem for StuckCounter {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![counter_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.bv_const(8, 0)?;
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let zero = arena.bv_const(8, 0)?;
        let one = arena.bv_const(8, 1)?;
        let is_zero = arena.eq(x, zero)?;
        let inc = arena.bv_add(x, one)?;
        let next_val = arena.ite(is_zero, zero, inc)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, next_val)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let c = arena.bv_const(8, self.target)?;
        Ok(arena.eq(x, c)?)
    }
}

/// A plain wrapping width-8 counter: `init: x = 0`, `trans: x' = x + 1`,
/// `bad: x == target`. Reachable in `target` steps ⇒ **unsafe**.
struct WrappingCounter {
    target: u128,
}

impl TransitionSystem for WrappingCounter {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![counter_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.bv_const(8, 0)?;
        Ok(arena.eq(x, zero)?)
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

/// A width-8 register stepping by +2 from 0; `bad`: the value is odd. "`x` even"
/// is genuinely *inductive* (even + 2 is even), so this is k-inductive at `k = 0`
/// — a sanity case `IMC` must also prove `Safe`.
struct EvenStepper;

impl TransitionSystem for EvenStepper {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![counter_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.bv_const(8, 0)?;
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let two = arena.bv_const(8, 2)?;
        let inc = arena.bv_add(x, two)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let one = arena.bv_const(8, 1)?;
        let lsb = arena.bv_and(x, one)?;
        Ok(arena.eq(lsb, one)?)
    }
}

/// Independently re-checks the three inductive-invariant conditions of a candidate
/// `invariant` against `system`, each via the trusted [`check_auto`] decider. The
/// test-side soundness audit: it does **not** trust the engine's verdict.
fn invariant_passes_three_checks(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    invariant: TermId,
) -> bool {
    let config = SolverConfig::default();
    let s = system.state_vars(arena, 0).unwrap();
    let sp = system.state_vars(arena, 1).unwrap();

    // 1. Initiation: init(s) ∧ ¬Inv(s) must be UNSAT.
    let init = system.init(arena, &s).unwrap();
    let not_inv = arena.not(invariant).unwrap();
    let initiation = matches!(
        check_auto(arena, &[init, not_inv], &config),
        Ok(CheckResult::Unsat)
    );

    // 2. Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s') must be UNSAT.
    let inv_primed = prime_term(arena, invariant, &s, &sp);
    let trans = system.trans(arena, &s, &sp).unwrap();
    let not_inv_primed = arena.not(inv_primed).unwrap();
    let consecution = matches!(
        check_auto(arena, &[invariant, trans, not_inv_primed], &config),
        Ok(CheckResult::Unsat)
    );

    // 3. Safety: Inv(s) ∧ bad(s) must be UNSAT.
    let bad = system.bad(arena, &s).unwrap();
    let safety = matches!(
        check_auto(arena, &[invariant, bad], &config),
        Ok(CheckResult::Unsat)
    );

    initiation && consecution && safety
}

/// Rebuilds `term` (over `s`) using the primed copy `sp`, by structural symbol
/// substitution `s[i] ↦ sp[i]` — the test-side mirror of the engine's primer.
fn prime_term(arena: &mut TermArena, term: TermId, s: &[SymbolId], sp: &[SymbolId]) -> TermId {
    use axeyum_ir::TermNode;
    match arena.node(term).clone() {
        TermNode::App { args, .. } => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&arg| prime_term(arena, arg, s, sp))
                .collect();
            arena.rebuild_with_args(term, &new_args)
        }
        TermNode::Symbol(sym) => match s.iter().position(|&x| x == sym) {
            Some(i) => arena.var(sp[i]),
            None => term,
        },
        _ => term,
    }
}

#[test]
fn imc_discovers_invariant_where_k_induction_is_inconclusive() {
    let system = StuckCounter { target: 6 };

    // First, witness the *gap*: k-induction is genuinely inconclusive at small k.
    let mut arena = TermArena::new();
    let k_outcome =
        prove_safety_k_induction(&mut arena, &system, 3, &SolverConfig::default()).unwrap();
    assert!(
        matches!(k_outcome, SafetyOutcome::Inconclusive { .. }),
        "‘x = 0 stays 0; bad = 6’ is not 3-inductive, so k-induction must be Inconclusive, got \
         {k_outcome:?}"
    );

    // IMC must close the same property by growing an interpolant over-approximation.
    let mut arena = TermArena::new();
    let outcome = prove_safety_imc(&mut arena, &system, &SolverConfig::default()).unwrap();
    let ImcOutcome::Safe { invariant } = outcome else {
        panic!("expected IMC to discover an invariant and report Safe, got {outcome:?}");
    };

    // Do NOT trust the verdict: independently re-check the three inductive
    // conditions via check_auto. A wrong Safe fails here.
    assert!(
        invariant_passes_three_checks(&mut arena, &system, invariant),
        "the IMC-discovered invariant must independently pass initiation, consecution, and safety"
    );
}

#[test]
fn imc_reports_reachable_for_an_unsafe_system() {
    let system = WrappingCounter { target: 5 };
    let mut arena = TermArena::new();
    let outcome = prove_safety_imc(&mut arena, &system, &SolverConfig::default()).unwrap();
    let ImcOutcome::Reachable { steps, model } = outcome else {
        panic!("expected Reachable for an unsafe counter, got {outcome:?}");
    };
    assert_eq!(steps, 5, "0 → 5 is exactly five increments");

    // Cross-check against the trusted BMC: it must agree, with a replay-checked
    // model.
    let mut arena = TermArena::new();
    let bmc = bounded_model_check(&mut arena, &system, 10, &SolverConfig::default()).unwrap();
    assert!(
        matches!(bmc, BmcOutcome::Reachable { steps: 5, .. }),
        "BMC must confirm the same reachable counterexample, got {bmc:?}"
    );
    assert!(
        !model.is_empty(),
        "the counterexample model assigns state vars"
    );
}

#[test]
fn imc_proves_a_k_inductive_system_safe() {
    let mut arena = TermArena::new();
    let outcome = prove_safety_imc(&mut arena, &EvenStepper, &SolverConfig::default()).unwrap();
    let ImcOutcome::Safe { invariant } = outcome else {
        panic!("expected Safe for the k-inductive even-stepper, got {outcome:?}");
    };
    assert!(
        invariant_passes_three_checks(&mut arena, &EvenStepper, invariant),
        "the discovered invariant must independently pass all three checks"
    );
}

#[test]
fn imc_declines_to_unknown_under_a_tight_timeout() {
    // A nanosecond timeout must force a graceful Unknown, never a hang or a panic,
    // and never a wrong Safe/Reachable. Use a harder (longer-chain) target so the
    // search cannot trivially finish before the deadline.
    let system = StuckCounter { target: 200 };
    let config = SolverConfig {
        timeout: Some(Duration::from_nanos(1)),
        ..SolverConfig::default()
    };
    let mut arena = TermArena::new();
    let outcome = prove_safety_imc(&mut arena, &system, &config).unwrap();
    // Either it declines (expected under the nanosecond cap) or — if it somehow
    // finished first — it returns a *verified* Safe. Both are sound; a wrong
    // verdict is not.
    match outcome {
        ImcOutcome::Unknown { .. } => {}
        ImcOutcome::Safe { invariant } => {
            assert!(
                invariant_passes_three_checks(&mut arena, &system, invariant),
                "a Safe under the cap must still be a verified invariant"
            );
        }
        ImcOutcome::Reachable { .. } => panic!("target 200 is unreachable; Reachable is wrong"),
    }
}
