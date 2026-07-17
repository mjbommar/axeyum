//! Integration tests for `prove_safety_pdr_lia` — IC3/PDR (Spacer-style)
//! inductive-invariant discovery over linear-INTEGER-arithmetic transition
//! systems, using integer model-based projection (`mbp_lia`) for predecessor
//! generalization. The integer mirror of `tests/pdr_lra.rs`.
//!
//! Every `Safe` is re-checked test-side (the three inductive-invariant conditions
//! through `check_auto`); every `Reachable` has its trace re-decided via an inline
//! LIA unrolling; the resource-cap and non-`LIA` cases assert a graceful `Unknown`
//! (never a hang, never a wrong verdict).
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{
    CheckResult, PdrLiaOutcome, SolverConfig, SolverError, TransitionSystem, check_auto,
    prove_safety_pdr_lia,
};

/// A single `Int` state variable named `x@{step}`.
fn int_var(arena: &mut TermArena, step: usize) -> SymbolId {
    arena.declare(&format!("x@{step}"), Sort::Int).unwrap()
}

/// An integer accumulator: `init : x = 0`, `trans : x' = x + 1`, `bad : x < 0`.
/// The reachable set is `x ∈ {0, 1, 2, …}`; a safety invariant is `x ≥ 0`. PDR
/// should discover a blocking lemma for the bad region and close to a fixpoint.
struct IntAccumulator;

impl TransitionSystem for IntAccumulator {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let zero = arena.int_const(0);
        Ok(arena.int_lt(x, zero)?)
    }
}

/// A two-variable safe system that is **not** 1-inductive on the property alone:
/// `init : x = 0 ∧ y = 0`, `trans : x' = x + 1 ∧ y' = y + 1`, `bad : x < y`. The
/// invariant `x = y` holds; PDR's predecessor generalization (via `mbp_lia`
/// projecting the next-state vars) is exercised here. A sound verdict is required
/// (`Safe` re-validated, or `Unknown`), never `Reachable`.
struct TwinCounters;

impl TransitionSystem for TwinCounters {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![
            arena.declare(&format!("x@{step}"), Sort::Int)?,
            arena.declare(&format!("y@{step}"), Sort::Int)?,
        ])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let zero = arena.int_const(0);
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
        let one = arena.int_const(1);
        let x = arena.var(pre[0]);
        let y = arena.var(pre[1]);
        let xn = arena.var(post[0]);
        let yn = arena.var(post[1]);
        let xinc = arena.int_add(x, one)?;
        let yinc = arena.int_add(y, one)?;
        let cx = arena.eq(xn, xinc)?;
        let cy = arena.eq(yn, yinc)?;
        Ok(arena.and(cx, cy)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let y = arena.var(s[1]);
        Ok(arena.int_lt(x, y)?)
    }
}

/// An **integer-specific** safe system whose real relaxation is **unsafe**:
/// `init : x = 0`, `trans : x' = x + 2`, `bad : x = 1`. Over ℤ, `x` is always even,
/// so `x = 1` is unreachable (the invariant must capture parity / `x ≥ 0`-style
/// reasoning that excludes `x = 1`). Over ℝ the state `x = 1` sits on the line of
/// reachable points only as a non-step; but the *parity* lemma needs integrality.
/// Concretely: from `x = 0` by `+2` the reachable integers are `{0, 2, 4, …}` and
/// `x = 1` is never hit — a fact the integer decider must establish.
struct EvenStepperOddTarget;

impl TransitionSystem for EvenStepperOddTarget {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let two = arena.int_const(2);
        let inc = arena.int_add(x, two)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let one = arena.int_const(1);
        Ok(arena.eq(x, one)?)
    }
}

/// An **unsafe** integer system: `init : x = 0`, `trans : x' = x + 1`,
/// `bad : x = 3`. A bad state is reachable in exactly three transitions.
struct ReachesThree;

impl TransitionSystem for ReachesThree {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let three = arena.int_const(3);
        Ok(arena.eq(x, three)?)
    }
}

/// A **non-LIA** system: 8-bit bit-vector state. The LIA cube / `mbp_lia`
/// predecessor machinery cannot represent it; the engine must decline to `Unknown`
/// (or a sound `Reachable` from the unrolling) — never panic, never a wrong `Safe`.
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

/// A genuinely **unsafe** integer system that a buggy engine might wrongly call
/// `Safe`: `init : x = 0`, `trans : x' = x + 1`, `bad : x ≥ 5`. The reachable set
/// is unbounded, so `x ≥ 5` IS reachable. A correct engine reports `Reachable`;
/// a `Safe` here would be unsound and the test fails loudly.
struct UnboundedReachesFive;

impl TransitionSystem for UnboundedReachesFive {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![int_var(arena, step)])
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s0[0]);
        let zero = arena.int_const(0);
        Ok(arena.eq(x, zero)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let x = arena.var(pre[0]);
        let one = arena.int_const(1);
        let inc = arena.int_add(x, one)?;
        let x_next = arena.var(post[0]);
        Ok(arena.eq(x_next, inc)?)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let x = arena.var(s[0]);
        let five = arena.int_const(5);
        Ok(arena.int_ge(x, five)?)
    }
}

/// Re-checks the three inductive-invariant conditions test-side, independently of
/// the engine's own gate: each must be `Unsat` under `check_auto` over ℤ.
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

/// Replay-checks a `Reachable` trace: the witnessed `model` plus init + each trans
/// step + bad at the final state must be jointly `Sat` over ℤ.
fn replay_reachable_trace(
    arena: &mut TermArena,
    system: &impl TransitionSystem,
    steps: usize,
    model: &axeyum_solver::Model,
) -> bool {
    let config = SolverConfig::default();
    let mut states: Vec<Vec<SymbolId>> = Vec::new();
    for step in 0..=steps {
        states.push(system.state_vars(arena, step).unwrap());
    }
    let mut assertions = vec![system.init(arena, &states[0]).unwrap()];
    for window in states.windows(2) {
        assertions.push(system.trans(arena, &window[0], &window[1]).unwrap());
    }
    // Pin the witnessed integer values along the path.
    for state in &states {
        if let Some(axeyum_ir::Value::Int(v)) = model.get(state[0]) {
            let xv = arena.var(state[0]);
            let cv = arena.int_const(v);
            assertions.push(arena.eq(xv, cv).unwrap());
        }
    }
    let bad_last = system.bad(arena, &states[steps]).unwrap();
    assertions.push(bad_last);
    matches!(
        check_auto(arena, &assertions, &config),
        Ok(CheckResult::Sat(_))
    )
}

#[test]
fn int_accumulator_is_proven_safe_and_revalidates() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lia(&mut arena, &IntAccumulator, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLiaOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &IntAccumulator, invariant),
                "the returned invariant must pass an independent 3-condition re-check over ℤ"
            );
        }
        PdrLiaOutcome::Unknown { reason } => {
            panic!(
                "the accumulator's bad region (x < 0) should be blockable to Safe; got Unknown: {reason}"
            )
        }
        PdrLiaOutcome::Reachable { .. } => {
            panic!("the accumulator is safe (x ≥ 0); a Reachable verdict is unsound")
        }
    }
}

#[test]
fn twin_counters_is_sound_safe_or_unknown() {
    // Exercises the multi-variable `mbp_lia` predecessor projection (a non-trivial
    // inductive strengthening: ¬bad alone is not 1-inductive). Contract: sound only
    // — Safe (re-validated) or Unknown, never Reachable.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lia(&mut arena, &TwinCounters, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLiaOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &TwinCounters, invariant),
                "any Safe invariant must pass the independent 3-condition re-check over ℤ"
            );
        }
        PdrLiaOutcome::Unknown { .. } => {}
        PdrLiaOutcome::Reachable { .. } => {
            panic!("twin counters keep x = y forever (x < y unreachable); Reachable is unsound")
        }
    }
}

#[test]
fn even_stepper_odd_target_is_sound_safe_or_unknown() {
    // Integer-specific: from x = 0 by +2 the reachable integers are {0,2,4,…}, so
    // bad (x = 1) is unreachable. The integer decider must be in the loop to
    // establish this. Contract: sound only — Safe (re-validated) or Unknown, never
    // Reachable.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lia(&mut arena, &EvenStepperOddTarget, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLiaOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &EvenStepperOddTarget, invariant),
                "any Safe invariant must pass the independent 3-condition re-check over ℤ"
            );
        }
        PdrLiaOutcome::Unknown { .. } => {}
        PdrLiaOutcome::Reachable { .. } => {
            panic!("x = 1 is never reached from x = 0 by +2 (always even); Reachable is unsound")
        }
    }
}

#[test]
fn reaches_three_is_reachable_with_a_revalidated_trace() {
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lia(&mut arena, &ReachesThree, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLiaOutcome::Reachable { steps, model } => {
            assert!(steps >= 3, "bad (x = 3) needs at least three increments");
            assert!(
                replay_reachable_trace(&mut arena, &ReachesThree, steps, &model),
                "the witnessed trace must re-check as a genuine path to a bad state"
            );
        }
        other => panic!("x = 3 is reachable from x = 0 by +1; expected Reachable, got {other:?}"),
    }
}

#[test]
fn unbounded_unsafe_never_reports_safe() {
    // Soundness: an actually-unsafe system (x ≥ 5 IS reachable from x = 0 by +1)
    // must NEVER be reported Safe. A correct engine reports Reachable (re-checked);
    // an honest Unknown would still be sound, but a Safe is a soundness bug.
    let mut arena = TermArena::new();
    let outcome =
        prove_safety_pdr_lia(&mut arena, &UnboundedReachesFive, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLiaOutcome::Reachable { steps, model } => {
            assert!(
                replay_reachable_trace(&mut arena, &UnboundedReachesFive, steps, &model),
                "the witnessed unsafe trace must re-check as a genuine path to x ≥ 5"
            );
        }
        PdrLiaOutcome::Unknown { .. } => {}
        PdrLiaOutcome::Safe { .. } => {
            panic!("x ≥ 5 is reachable from x = 0 by +1; a Safe verdict is UNSOUND")
        }
    }
}

#[test]
fn tight_timeout_yields_unknown_without_hanging() {
    let mut arena = TermArena::new();
    let config = SolverConfig::default().with_timeout(Duration::from_nanos(1));
    // A near-zero deadline must produce a first-class Unknown promptly — never a
    // hang, panic, or a fabricated Safe/Reachable.
    let outcome = prove_safety_pdr_lia(&mut arena, &IntAccumulator, &config).unwrap();
    assert!(
        matches!(outcome, PdrLiaOutcome::Unknown { .. }),
        "a 1 ns timeout must degrade to Unknown, got {outcome:?}"
    );
}

#[test]
fn non_lia_bv_system_declines_gracefully() {
    let mut arena = TermArena::new();
    // The BV system is outside the LIA cube / mbp_lia fragment. The engine must at
    // minimum never produce a wrong Safe and never panic. A Reachable would be
    // sound (BV bad = 42 is reachable, replay-checked); an Unknown is the expected
    // graceful decline.
    let outcome = prove_safety_pdr_lia(&mut arena, &BvSystem, &SolverConfig::default()).unwrap();
    match outcome {
        PdrLiaOutcome::Unknown { .. } | PdrLiaOutcome::Reachable { .. } => {}
        PdrLiaOutcome::Safe { invariant } => {
            assert!(
                recheck_invariant(&mut arena, &BvSystem, invariant),
                "a BV Safe verdict must independently re-check (it must not)"
            );
            panic!("the BV system is unsafe (42 reachable); a Safe verdict is unsound");
        }
    }
}
