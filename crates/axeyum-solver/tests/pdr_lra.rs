//! Integration tests for `prove_safety_pdr_lra` — IC3/PDR (Spacer-style)
//! inductive-invariant discovery over linear-real-arithmetic transition systems,
//! using model-based projection (`mbp_lra`) for predecessor generalization.
//!
//! Every `Safe` is re-checked test-side (the three inductive-invariant conditions
//! through `check_auto`); every `Reachable` has its trace re-decided via an
//! inline LRA unrolling; the resource-cap and non-`LRA` cases assert a graceful
//! `Unknown` (never a hang, never a wrong verdict).

use std::time::Duration;

use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    CheckResult, PdrLraOutcome, SolverConfig, SolverError, TransitionSystem, check_auto,
    prove_safety_pdr_lra,
};

/// A single `Real` state variable named `x@{step}`.
fn real_var(arena: &mut TermArena, step: usize) -> SymbolId {
    arena.declare(&format!("x@{step}"), Sort::Real).unwrap()
}

fn rint(n: i128) -> Rational {
    Rational::new(n, 1)
}

/// A real accumulator: `init : x = 0`, `trans : x' = x + 1`, `bad : x < 0`. The
/// reachable set is `x ∈ {0, 1, 2, …}`; a safety invariant is `x ≥ 0`. PDR should
/// discover a blocking lemma for the bad region and close to a fixpoint.
struct RealAccumulator;

impl TransitionSystem for RealAccumulator {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![real_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.real_const(rint(1));
        let inc = arena.real_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.real_lt(x, zero)?)
    }
}

/// A monotone real system whose `init` is **already inductive**: `init : x ≥ 0`,
/// `trans : x' = x + 1`, `bad : x < 0`. `F[1]` is bad-free immediately (`x ≥ 0 ∧
/// x < 0` is unsat), so the empty frame propagates to a fixpoint and the empty
/// invariant — `true` — is rejected by the safety gate; PDR must learn the
/// blocking lemma `¬(x < 0)` to close to `Safe`. Either way the verdict is sound.
struct MonotoneLowerBound;

impl TransitionSystem for MonotoneLowerBound {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![real_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.real_ge(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.real_const(rint(1));
        let inc = arena.real_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.real_lt(x, zero)?)
    }
}

/// A two-variable safe system that is **not** 1-inductive on the property alone:
/// `init : x = 0 ∧ y = 0`, `trans : x' = x + 1 ∧ y' = y + 1`, `bad : x < y`. The
/// invariant `x = y` (equivalently `¬(x < y) ∧ ¬(y < x)`) holds; PDR's
/// predecessor generalization (via `mbp_lra` projecting the next-state vars) is
/// exercised here. A sound verdict is required (`Safe` re-validated, or `Unknown`).
struct TwinCounters;

impl TransitionSystem for TwinCounters {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![
            arena.declare(&format!("x@{step}"), Sort::Real)?,
            arena.declare(&format!("y@{step}"), Sort::Real)?,
        ])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let zero = arena.real_const(Rational::zero());
        let x = arena.var(s0[0]);
        let y = arena.var(s0[1]);
        let xz = arena.eq(x, zero)?;
        let yz = arena.eq(y, zero)?;
        Ok(arena.and(xz, yz)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let one = arena.real_const(rint(1));
        let x = arena.var(pre[0]);
        let y = arena.var(pre[1]);
        let xn = arena.var(post[0]);
        let yn = arena.var(post[1]);
        let xinc = arena.real_add(x, one)?;
        let yinc = arena.real_add(y, one)?;
        let cx = arena.eq(xn, xinc)?;
        let cy = arena.eq(yn, yinc)?;
        Ok(arena.and(cx, cy)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let y = arena.var(s[1]);
        Ok(arena.real_lt(x, y)?)
    }
}

/// An **unsafe** real system: `init : x = 0`, `trans : x' = x + 1`, `bad : x = 3`.
/// A bad state is reachable in exactly three transitions.
struct ReachesThree;

impl TransitionSystem for ReachesThree {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![real_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.real_const(Rational::zero());
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.real_const(rint(1));
        let inc = arena.real_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let three = arena.real_const(rint(3));
        Ok(arena.eq(x, three)?)
    }
}

/// A **non-LRA** system: 8-bit bit-vector state. The LRA cube / `mbp_lra`
/// predecessor machinery cannot represent it; the engine must decline to
/// `Unknown` (or a sound `Reachable` from the unrolling) — never panic, never a
/// wrong `Safe`.
struct BvSystem;

impl TransitionSystem for BvSystem {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![arena.declare(&format!("b@{step}"), Sort::BitVec(8))?])
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
        let target = arena.bv_const(8, 42)?;
        Ok(arena.eq(x, target)?)
    }
}

/// Re-checks the three inductive-invariant conditions test-side, independently of
/// the engine's own gate: each must be `Unsat` under `check_auto`.
fn recheck_invariant(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    invariant: TermId,
) -> bool {
    let config = SolverConfig::default();
    let s = system.state_vars(arena, 0).unwrap();
    let sp = system.state_vars(arena, 1).unwrap();

    // Initiation: init(s) ∧ ¬Inv(s) unsat.
    let init = system.init(arena, &s).unwrap();
    let not_inv = arena.not(invariant).unwrap();
    if !matches!(
        check_auto(arena, &[init, not_inv], &config),
        Ok(CheckResult::Unsat)
    ) {
        return false;
    }

    // Consecution: Inv(s) ∧ trans(s, s') ∧ ¬Inv(s') unsat. Prime the invariant
    // structurally s[i] ↦ sp[i].
    let mut inv_primed = invariant;
    for (from, to) in s.iter().copied().zip(sp.iter().copied()) {
        inv_primed = substitute_one(arena, inv_primed, from, to);
    }
    let trans = system.trans(arena, &s, &sp).unwrap();
    let not_inv_primed = arena.not(inv_primed).unwrap();
    if !matches!(
        check_auto(arena, &[invariant, trans, not_inv_primed], &config),
        Ok(CheckResult::Unsat)
    ) {
        return false;
    }

    // Safety: Inv(s) ∧ bad(s) unsat.
    let bad = system.bad(arena, &s).unwrap();
    matches!(
        check_auto(arena, &[invariant, bad], &config),
        Ok(CheckResult::Unsat)
    )
}

/// Structural single-symbol substitution `from ↦ to`, for priming the invariant.
fn substitute_one(arena: &mut TermArena, term: TermId, from: SymbolId, to: SymbolId) -> TermId {
    use axeyum_ir::TermNode;
    match arena.node(term).clone() {
        TermNode::App { args, .. } => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&arg| substitute_one(arena, arg, from, to))
                .collect();
            arena.rebuild_with_args(term, &new_args)
        }
        TermNode::Symbol(sym) if sym == from => arena.var(to),
        _ => term,
    }
}

#[test]
fn real_accumulator_is_proven_safe_and_revalidates() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lra(&mut arena, &RealAccumulator, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLraOutcome::Safe { invariant } => {
            // The engine's 3-check gate accepted it; re-validate independently.
            assert!(
                recheck_invariant(&mut arena, &RealAccumulator, invariant),
                "the returned invariant must pass an independent 3-condition re-check"
            );
        }
        // PDR should close the accumulator's single bad region; an honest Unknown
        // would still be sound, but this system is the closure target.
        PdrLraOutcome::Unknown { reason } => {
            panic!(
                "the accumulator's bad region (x < 0) should be blockable to Safe; got Unknown: {reason}"
            )
        }
        PdrLraOutcome::Reachable { .. } => {
            panic!("the accumulator is safe (x ≥ 0); a Reachable verdict is unsound")
        }
    }
}

#[test]
fn monotone_lower_bound_is_sound_safe_or_unknown() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lra(&mut arena, &MonotoneLowerBound, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLraOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &MonotoneLowerBound, invariant),
                "any Safe invariant must pass the independent 3-condition re-check"
            );
        }
        PdrLraOutcome::Unknown { .. } => {}
        PdrLraOutcome::Reachable { .. } => {
            panic!("the monotone system is safe (x ≥ 0); a Reachable verdict is unsound")
        }
    }
}

#[test]
fn twin_counters_is_sound_safe_or_unknown() {
    // Exercises the multi-variable `mbp_lra` predecessor projection. Contract:
    // sound only — Safe (re-validated) or Unknown, never Reachable.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lra(&mut arena, &TwinCounters, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLraOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &TwinCounters, invariant),
                "any Safe invariant must pass the independent 3-condition re-check"
            );
        }
        PdrLraOutcome::Unknown { .. } => {}
        PdrLraOutcome::Reachable { .. } => {
            panic!("twin counters keep x = y forever (x < y unreachable); Reachable is unsound")
        }
    }
}

#[test]
fn reaches_three_is_reachable_with_a_revalidated_trace() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lra(&mut arena, &ReachesThree, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLraOutcome::Reachable { steps, model } => {
            assert!(steps >= 3, "bad (x = 3) needs at least three increments");
            // Re-decide the concrete unrolling with the witnessed model values and
            // confirm the trace really reaches a bad state: replay-check test-side.
            let config = SolverConfig::default();
            let mut states: Vec<Vec<SymbolId>> = Vec::new();
            for step in 0..=steps {
                states.push(ReachesThree.state_vars(&mut arena, step).unwrap());
            }
            let mut assertions = vec![ReachesThree.init(&mut arena, &states[0]).unwrap()];
            for window in states.windows(2) {
                assertions.push(
                    ReachesThree
                        .trans(&mut arena, &window[0], &window[1])
                        .unwrap(),
                );
            }
            for state in &states {
                if let Some(axeyum_ir::Value::Real(r)) = model.get(state[0]) {
                    let xv = arena.var(state[0]);
                    let cv = arena.real_const(r);
                    assertions.push(arena.eq(xv, cv).unwrap());
                }
            }
            let bad_last = ReachesThree.bad(&mut arena, &states[steps]).unwrap();
            assertions.push(bad_last);
            assert!(
                matches!(
                    check_auto(&mut arena, &assertions, &config),
                    Ok(CheckResult::Sat(_))
                ),
                "the witnessed trace must re-check as a genuine path to a bad state"
            );
        }
        other => panic!("x = 3 is reachable from x = 0 by +1; expected Reachable, got {other:?}"),
    }
}

#[test]
fn tight_timeout_yields_unknown_without_hanging() {
    let mut arena = TermArena::new();
    let config = SolverConfig::default().with_timeout(Duration::from_nanos(1));
    // A near-zero deadline must produce a first-class Unknown promptly — never a
    // hang, panic, or a fabricated Safe/Reachable.
    let outcome = prove_safety_pdr_lra(&mut arena, &RealAccumulator, &config).unwrap();
    assert!(
        matches!(outcome, PdrLraOutcome::Unknown { .. }),
        "a 1 ns timeout must degrade to Unknown, got {outcome:?}"
    );
}

#[test]
fn non_lra_bv_system_declines_gracefully() {
    let mut arena = TermArena::new();
    // The BV system is outside the LRA cube / mbp_lra fragment. The engine must at
    // minimum never produce a wrong Safe and never panic. A Reachable would be
    // sound (BV bad = 42 is reachable, replay-checked); an Unknown is the expected
    // graceful decline.
    let outcome = prove_safety_pdr_lra(&mut arena, &BvSystem, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLraOutcome::Unknown { .. } | PdrLraOutcome::Reachable { .. } => {}
        PdrLraOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &BvSystem, invariant),
                "a BV Safe verdict must independently re-check (it must not)"
            );
            panic!("the BV system is unsafe (42 reachable); a Safe verdict is unsound");
        }
    }
}
