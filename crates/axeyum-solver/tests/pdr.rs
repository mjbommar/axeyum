//! Integration tests for the `IC3`/`PDR` inductive-invariant-discovery engine.
//!
//! The soundness theme runs through every test: a `Safe` verdict is never trusted
//! on the engine's say-so — each safe test **independently re-checks** the
//! returned invariant's three implication conditions (initiation, consecution,
//! safety) with [`check_auto`], and the `Reachable` test cross-checks against
//! [`bounded_model_check`]. A wrong `Safe`/`Reachable` would fail these
//! independent checks; an over-eager `Unknown` is acceptable.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    BmcOutcome, CertifiedPdrOutcome, CheckResult, PdrOutcome, SafetyOutcome, SolverConfig,
    SolverError, TransitionSystem, bounded_model_check, check_auto, prove_safety_k_induction,
    prove_safety_pdr, prove_safety_pdr_certified,
};
use std::time::Duration;

/// A width-8 counter that is **stuck at 0** once it leaves the initial state's
/// only successor: `init: x = 0`, `trans: x' = ite(x == 0, 0, x + 1)`. The only
/// reachable state is `x = 0`. `bad: x == target`.
///
/// For a `target` in `1..=12` this is *safe* (target is unreachable) but **not**
/// k-inductive for any small `k`: from the unreachable-but-good state
/// `x = target-1` the transition steps straight into the bad state, and a chain of
/// `target-1` consecutive good states `1,2,…,target-1` precedes it — so the
/// inductive step never closes at small `k`. The real inductive invariant is
/// `x ∉ {1,…,target}` (equivalently `x = 0` is the reachable set), which `PDR`
/// must *discover* — exactly the gap over k-induction.
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
        // x' = ite(x == 0, 0, x + 1)
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
/// `bad: x == target`. A bad `target` reachable in `target` steps makes this
/// **unsafe** — `PDR` must report `Reachable` (confirmed by `BMC`).
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
/// — a sanity case `PDR` must also prove `Safe`.
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
/// `invariant` against `system`, each via the trusted [`check_auto`] decider. This
/// is the test-side soundness audit: it does **not** trust the engine's verdict.
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

    // 2. Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s') must be UNSAT. The primed
    //    invariant is rebuilt by substituting s[i] ↦ sp[i] structurally.
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
fn pdr_discovers_invariant_where_k_induction_is_inconclusive() {
    let system = StuckCounter { target: 12 };

    // First, witness the *gap*: k-induction is genuinely inconclusive at small k.
    let mut arena = TermArena::new();
    let k_outcome =
        prove_safety_k_induction(&mut arena, &system, 5, &SolverConfig::default()).unwrap();
    assert!(
        matches!(k_outcome, SafetyOutcome::Inconclusive { .. }),
        "‘x = 0 stays 0; bad = 12’ is not 5-inductive, so k-induction must be Inconclusive, got \
         {k_outcome:?}"
    );

    // PDR must close the same property by discovering an inductive invariant.
    let mut arena = TermArena::new();
    let outcome = prove_safety_pdr(&mut arena, &system, &SolverConfig::default()).unwrap();
    let PdrOutcome::Safe { invariant } = outcome else {
        panic!("expected PDR to discover an invariant and report Safe, got {outcome:?}");
    };

    // Do NOT trust the verdict: independently re-check the invariant's three
    // inductive conditions via check_auto. A wrong Safe fails here.
    assert!(
        invariant_passes_three_checks(&mut arena, &system, invariant),
        "the PDR-discovered invariant must independently pass initiation, consecution, and safety"
    );
}

#[test]
fn pdr_reports_reachable_for_an_unsafe_system() {
    let system = WrappingCounter { target: 5 };
    let mut arena = TermArena::new();
    let outcome = prove_safety_pdr(&mut arena, &system, &SolverConfig::default()).unwrap();
    let PdrOutcome::Reachable { steps, model } = outcome else {
        panic!("expected Reachable for an unsafe counter, got {outcome:?}");
    };
    assert_eq!(steps, 5, "0 → 5 is exactly five increments");

    // Cross-check the verdict against the trusted BMC: it must agree that a bad
    // state is reachable, with a replay-checked model.
    let mut arena = TermArena::new();
    let bmc = bounded_model_check(&mut arena, &system, 10, &SolverConfig::default()).unwrap();
    assert!(
        matches!(bmc, BmcOutcome::Reachable { steps: 5, .. }),
        "BMC must confirm the same reachable counterexample, got {bmc:?}"
    );
    // The PDR model is non-empty (a genuine witnessed assignment).
    assert!(
        !model.is_empty(),
        "the counterexample model assigns state vars"
    );
}

#[test]
fn pdr_proves_a_k_inductive_system_safe() {
    let mut arena = TermArena::new();
    let outcome = prove_safety_pdr(&mut arena, &EvenStepper, &SolverConfig::default()).unwrap();
    let PdrOutcome::Safe { invariant } = outcome else {
        panic!("expected Safe for the k-inductive even-stepper, got {outcome:?}");
    };
    assert!(
        invariant_passes_three_checks(&mut arena, &EvenStepper, invariant),
        "the discovered invariant must independently pass all three checks"
    );
}

#[test]
fn pdr_declines_to_unknown_under_a_tight_timeout() {
    // A tiny timeout must force a graceful Unknown, never a hang or a panic, and
    // never a wrong Safe/Reachable. Use the harder (longer-chain) target so the
    // search cannot trivially finish before the deadline.
    let system = StuckCounter { target: 200 };
    let config = SolverConfig {
        timeout: Some(Duration::from_nanos(1)),
        ..SolverConfig::default()
    };
    let mut arena = TermArena::new();
    let outcome = prove_safety_pdr(&mut arena, &system, &config).unwrap();
    // Either it declines (expected under the nanosecond cap) or — if it somehow
    // finished first — it returns a *verified* Safe. Both are sound; a wrong
    // verdict is not. Assert it never panicked and, if Safe, the invariant checks.
    match outcome {
        PdrOutcome::Unknown { .. } => {}
        PdrOutcome::Safe { invariant } => {
            let config = SolverConfig::default();
            let _ = config;
            assert!(
                invariant_passes_three_checks(&mut arena, &system, invariant),
                "a Safe under the cap must still be a verified invariant"
            );
        }
        PdrOutcome::Reachable { .. } => panic!("target 200 is unreachable; Reachable is wrong"),
    }
}

#[test]
fn pdr_certified_bundles_recheckable_proofs_on_the_safe_case() {
    let system = StuckCounter { target: 12 };
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_certified(&mut arena, &system, &SolverConfig::default()).unwrap();
    let CertifiedPdrOutcome::Safe(cert) = outcome else {
        panic!("expected a certified Safe verdict, got {outcome:?}");
    };
    // Each obligation carries non-empty certificate text, and the whole bundle
    // re-checks independently through the consumer-side entry point.
    for proof in [&cert.initiation, &cert.consecution, &cert.safety] {
        assert!(!proof.dimacs.is_empty() && !proof.drat.is_empty());
        assert!(proof.recheck().unwrap(), "each obligation must re-check");
    }
    assert!(
        cert.recheck().unwrap(),
        "the whole IC3/PDR certificate must re-check independently"
    );
    // And the bundled invariant must still pass the three semantic checks.
    assert!(
        invariant_passes_three_checks(&mut arena, &system, cert.invariant),
        "the certified invariant must independently pass all three checks"
    );
}
